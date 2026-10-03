import Chapter8ForcedIntegralExistence
import FullAuditChapter4Gronwall

open MeasureTheory Set
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Stability of a linear inhomogeneous Volterra equation with respect
to its coefficients. Only the reference solution needs an a priori bound. -/
theorem linear_path_stability {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (A B : ℝ → E →L[ℝ] E) (R S X Y : ℝ → E)
    (hcA : Continuous A) (hcB : Continuous B) (hcR : Continuous R) (hcS : Continuous S)
    (hcX : Continuous X) (hcY : Continuous Y)
    (T L C D Q : ℝ) (hT : 0 ≤ T) (hL : 0<L) (hC : 0 ≤ C) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hA : ∀ s,s∈Icc 0 T → ‖A s‖ ≤ L)
    (hAB : ∀ s,s∈Icc 0 T → ‖A s-B s‖ ≤ C)
    (hRS : ∀ s,s∈Icc 0 T → ‖R s-S s‖ ≤ D)
    (hYb : ∀ s,s∈Icc 0 T → ‖Y s‖ ≤ Q)
    (hX : ∀ s,s∈Icc 0 T → X s=∫ r in 0..s,A r (X r)+R r)
    (hY : ∀ s,s∈Icc 0 T → Y s=∫ r in 0..s,B r (Y r)+S r) :
    ∀ s,s∈Icc 0 T → ‖X s-Y s‖ ≤ T*Real.exp (L*T)*(C*Q+D) := by
  let e := fun s => X s-Y s
  let g := fun s => (A s (X s)+R s)-(B s (Y s)+S s)
  have hec : Continuous e := hcX.sub hcY
  have he s (hs : s∈Icc 0 T) : e s=∫ r in 0..s,g r := by
    dsimp only [e,g]
    rw [hX s hs,hY s hs,intervalIntegral.integral_sub
      (f := fun r => A r (X r)+R r) (g := fun r => B r (Y r)+S r)
      (((hcA.clm_apply hcX).add hcR).intervalIntegrable 0 s)
      (((hcB.clm_apply hcY).add hcS).intervalIntegrable 0 s)]
  have hgn s (hs : s∈Icc 0 T) : ‖g s‖ ≤ L*‖e s‖+(C*Q+D) := by
    have hg : g s=A s (e s)+(A s-B s) (Y s)+(R s-S s) := by
      dsimp [g,e]
      simp only [map_sub,ContinuousLinearMap.sub_apply]
      abel
    have h1 : ‖A s (e s)‖ ≤ L*‖e s‖ :=
      ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA s hs) (norm_nonneg _))
    have h2 : ‖(A s-B s) (Y s)‖ ≤ C*Q :=
      ((A s-B s).le_opNorm _).trans (mul_le_mul (hAB s hs) (hYb s hs) (norm_nonneg _) hC)
    rw [hg]
    have hh := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h1 h2)) (hRS s hs))
    exact hh.trans_eq (by ring)
  have hine s (hs : s∈Icc 0 T) : ‖e s‖ ≤ (C*Q+D)*T+L*∫ r in 0..s,‖e r‖ := by
    rw [he s hs]
    have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0:ℝ)) (b := s)
      (f := g) (g := fun r => L*‖e r‖+(C*Q+D)) hs.1
      (ae_of_all _ (fun r hr => hgn r ⟨hr.1.le,hr.2.trans hs.2⟩))
      (((hec.norm.const_mul L).add continuous_const).intervalIntegrable 0 s)
    rw [intervalIntegral.integral_add (f := fun r => L*‖e r‖) (g := fun _ => C*Q+D)
      ((hec.norm.const_mul L).intervalIntegrable 0 s) intervalIntegrable_const,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hh
    have ht := mul_le_mul_of_nonneg_left hs.2 (by positivity : 0 ≤ C*Q+D)
    linarith
  intro s hs
  have hh := ch4_gronwall_written (fun r => ‖e r‖) ((C*Q+D)*T) L T hT hec.norm.continuousOn hL hine s hs
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hL.le)
  have hh' := hh.trans (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (C*Q+D)*T))
  convert hh' using 1 <;> ring

end Asakura.Chapter8
