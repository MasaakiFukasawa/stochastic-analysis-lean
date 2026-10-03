import Chapter8QuadraticDerivativeCriterion
import FullAuditChapter4Gronwall

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The variational integral equation really gives the initial-state
derivative of an additive-noise solution. This is proved by the Taylor
remainder and Gronwall, rather than assuming differentiability of the flow. -/
theorem flow_initial_derivative_from_integral_equations {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : E → E) (D : E → E →L[ℝ] E) (hD : ∀ z,HasFDerivAt b (D z) z)
    (K : ℝ≥0) (hK : LipschitzWith K D) (L : ℝ) (hL : 0<L) (hDb : ∀ z,‖D z‖ ≤ L)
    (X : E → ℝ → E) (W : ℝ → E) (hcX : ∀ z,Continuous (X z))
    (x : E) (T A : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hX : ∀ z s,s∈Icc 0 T → X z s=z+(∫ r in 0..s,b (X z r))+W s)
    (hLip : ∀ h s,s∈Icc 0 T → ‖X (x+h) s-X x s‖ ≤ A*‖h‖)
    (J : ℝ → E →L[ℝ] E) (hcJ : Continuous J)
    (hJ : ∀ s,s∈Icc 0 T → ∀ h,J s h=h+∫ r in 0..s,D (X x r) (J r h)) :
    HasFDerivAt (fun z => X z T) (J T) x := by
  have hb : Continuous b := continuous_iff_continuousAt.mpr (fun z => (hD z).continuousAt)
  apply derivative_of_quadratic_remainder _ (J T) x
    ((K:ℝ)*A^2*T*Real.exp (L*T)) (by positivity)
  intro h
  let e := fun s => X (x+h) s-X x s-J s h
  let g := fun s => b (X (x+h) s)-b (X x s)-D (X x s) (J s h)
  have hec : Continuous e := ((hcX (x+h)).sub (hcX x)).sub (hcJ.clm_apply continuous_const)
  have hgc : Continuous g := ((hb.comp (hcX (x+h))).sub (hb.comp (hcX x))).sub
    ((hK.continuous.comp (hcX x)).clm_apply (hcJ.clm_apply continuous_const))
  have he s (hs : s∈Icc 0 T) : e s=∫ r in 0..s,g r := by
    dsimp only [e,g]
    rw [hX (x+h) s hs,hX x s hs,hJ s hs h]
    rw [intervalIntegral.integral_sub
      (f := fun r => b (X (x+h) r)-b (X x r)) (g := fun r => D (X x r) (J r h))
      (((hb.comp (hcX (x+h))).sub (hb.comp (hcX x))).intervalIntegrable 0 s)
      (((hK.continuous.comp (hcX x)).clm_apply (hcJ.clm_apply continuous_const)).intervalIntegrable 0 s),
      intervalIntegral.integral_sub (f := fun r => b (X (x+h) r)) (g := fun r => b (X x r))
        ((hb.comp (hcX (x+h))).intervalIntegrable 0 s)
        ((hb.comp (hcX x)).intervalIntegrable 0 s)]
    abel
  let B := (K:ℝ)*A^2*‖h‖^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hgn s (hs : s∈Icc 0 T) : ‖g s‖ ≤ L*‖e s‖+B := by
    have hrem := drift_quadratic_taylor_bound b D hD K hK (X (x+h) s) (X x s)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hLip h s hs) 2
    have hrem' : ‖b (X (x+h) s)-b (X x s)-D (X x s) (X (x+h) s-X x s)‖ ≤ B := by
      exact hrem.trans (by simpa only [B,mul_pow,mul_assoc] using
        mul_le_mul_of_nonneg_left hsq K.coe_nonneg)
    have hlin : ‖D (X x s) (e s)‖ ≤ L*‖e s‖ :=
      ((D (X x s)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hDb _) (norm_nonneg _))
    have hg : g s=D (X x s) (e s)+(b (X (x+h) s)-b (X x s)-D (X x s) (X (x+h) s-X x s)) := by
      dsimp only [g,e]
      simp only [map_sub]
      abel
    rw [hg]
    exact (norm_add_le _ _).trans (add_le_add hlin hrem')
  have hine s (hs : s∈Icc 0 T) : ‖e s‖ ≤ B*T+L*∫ r in 0..s,‖e r‖ := by
    rw [he s hs]
    have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0:ℝ)) (b := s)
      (f := g) (g := fun r => L*‖e r‖+B) hs.1
      (ae_of_all _ (fun r hr => hgn r ⟨hr.1.le,hr.2.trans hs.2⟩))
      (((hec.norm.const_mul L).add continuous_const).intervalIntegrable 0 s)
    rw [intervalIntegral.integral_add (f := fun r => L*‖e r‖) (g := fun _ => B)
      ((hec.norm.const_mul L).intervalIntegrable 0 s) intervalIntegrable_const,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hh
    have ht := mul_le_mul_of_nonneg_left hs.2 hB
    linarith
  have hh := ch4_gronwall_written (fun s => ‖e s‖) (B*T) L T hT hec.norm.continuousOn hL hine T ⟨hT,le_rfl⟩
  convert hh using 1 <;> dsimp only [e,B] <;> ring

end Asakura.Chapter8
