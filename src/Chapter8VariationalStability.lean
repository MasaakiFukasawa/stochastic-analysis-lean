import Chapter8VariationalBound
import FullAuditChapter4Gronwall

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The first variations are Lipschitz in their initial state, using
only a Lipschitz first drift derivative and deterministic bounds. -/
theorem variational_initial_stability {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (D : E → E →L[ℝ] E) (K : ℝ≥0) (hD : LipschitzWith K D)
    (X : E → ℝ → E) (J : E → ℝ → E →L[ℝ] E)
    (hcX : ∀ x,Continuous (X x)) (hcJ : ∀ x,Continuous (J x))
    (T A B L : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0<L)
    (hDb : ∀ x,‖D x‖ ≤ L)
    (hJb : ∀ x s,s∈Icc 0 T → ‖J x s‖ ≤ B)
    (hLip : ∀ x y s,s∈Icc 0 T → ‖X x s-X y s‖ ≤ A*‖x-y‖)
    (hJ : ∀ x s,s∈Icc 0 T → ∀ h,J x s h=h+∫ r in 0..s,D (X x r) (J x r h)) :
    ∀ x y s,s∈Icc 0 T →
      ‖J x s-J y s‖ ≤ ((K:ℝ)*A*B*T*Real.exp (L*T))*‖x-y‖ := by
  intro x y t ht
  have hc x : Continuous (fun s => D (X x s)*J x s) := (hD.continuous.comp (hcX x)).mul (hcJ x)
  have hJe x s (hs : s∈Icc 0 T) : J x s=1+∫ r in 0..s,D (X x r)*J x r := by
    ext h
    rw [hJ x s hs h]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply]
    rw [ContinuousLinearMap.intervalIntegral_apply (φ := fun r => D (X x r)*J x r)
      ((hc x).intervalIntegrable 0 s)]
    rfl
  let e := fun s => J x s-J y s
  let g := fun s => D (X x s)*J x s-D (X y s)*J y s
  let R := (K:ℝ)*A*B*‖x-y‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hec : Continuous e := (hcJ x).sub (hcJ y)
  have he s (hs : s∈Icc 0 T) : e s=∫ r in 0..s,g r := by
    dsimp only [e,g]
    rw [hJe x s hs,hJe y s hs,intervalIntegral.integral_sub (f := fun r => D (X x r)*J x r)
      (g := fun r => D (X y r)*J y r) ((hc x).intervalIntegrable 0 s) ((hc y).intervalIntegrable 0 s)]
    abel
  have hgn s (hs : s∈Icc 0 T) : ‖g s‖ ≤ L*‖e s‖+R := by
    have hg : g s=D (X x s)*e s+(D (X x s)-D (X y s))*J y s := by
      dsimp [g,e]
      noncomm_ring
    have hl : ‖D (X x s)*e s‖ ≤ L*‖e s‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hDb _) (norm_nonneg _))
    have hd := (hD.norm_sub_le (X x s) (X y s)).trans
      (mul_le_mul_of_nonneg_left (hLip x y s hs) K.coe_nonneg)
    have hr : ‖(D (X x s)-D (X y s))*J y s‖ ≤ R := by
      apply (norm_mul_le _ _).trans
      have hh := mul_le_mul hd (hJb y s hs) (norm_nonneg _) (by positivity : 0 ≤ (K:ℝ)*(A*‖x-y‖))
      convert hh using 1 <;> dsimp only [R] <;> ring
    rw [hg]
    exact (norm_add_le _ _).trans (add_le_add hl hr)
  have hine s (hs : s∈Icc 0 T) : ‖e s‖ ≤ R*T+L*∫ r in 0..s,‖e r‖ := by
    rw [he s hs]
    have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0:ℝ)) (b := s)
      (f := g) (g := fun r => L*‖e r‖+R) hs.1
      (ae_of_all _ (fun r hr => hgn r ⟨hr.1.le,hr.2.trans hs.2⟩))
      (((hec.norm.const_mul L).add continuous_const).intervalIntegrable 0 s)
    rw [intervalIntegral.integral_add (f := fun r => L*‖e r‖) (g := fun _ => R)
      ((hec.norm.const_mul L).intervalIntegrable 0 s) intervalIntegrable_const,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hh
    have ht := mul_le_mul_of_nonneg_left hs.2 hR
    linarith
  have hh := ch4_gronwall_written (fun s => ‖e s‖) (R*T) L T hT hec.norm.continuousOn hL hine t ht
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hL.le)
  have hh' := hh.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hR hT))
  convert hh' using 1 <;> dsimp only [e,R] <;> ring

end Asakura.Chapter8
