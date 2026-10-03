import Chapter8ActualTransitionRegularity
import Chapter8LipschitzGrowthData

open MeasureTheory Set
open scoped NNReal BigOperators
namespace Asakura.Chapter8
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2400000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

/-- The C3 hypothesis on U with bounded second and third derivatives
supplies every coefficient-regularity input in the Gibbs proof. -/
theorem potential_drift_regularity {d : ℕ}
    (U : (Fin d → ℝ) → ℝ) (hU : ContDiff ℝ 3 U)
    (A₂ A₃ : ℝ≥0)
    (h₂ : ∀ x,‖fderiv ℝ (fderiv ℝ U) x‖≤(A₂:ℝ))
    (h₃ : ∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ U)) x‖≤(A₃:ℝ))
    (M : Fin d → Fin d → ℝ) :
    ∃ (b : (Fin d → ℝ) → (Fin d → ℝ))
      (D : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
      (D₂ : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
      (C L : ℝ≥0) (Cg : ℝ),
      (∀ x i,b x i= -(∑ j,M i j*fderiv ℝ U x (Pi.single j 1))) ∧
      (∀ x,HasFDerivAt b (D x) x) ∧ (∀ x,HasFDerivAt D (D₂ x) x) ∧
      Continuous D₂ ∧ LipschitzWith C D ∧ 0<L ∧
      (∀ x,‖D x‖≤(L:ℝ)) ∧ 0≤Cg ∧
      (∀ i x,|fderiv ℝ U x (Pi.single i 1)|≤Cg*(1+‖x‖)) := by
  let E := Fin d → ℝ
  let A : (E →L[ℝ] ℝ) →L[ℝ] E :=
    ContinuousLinearMap.pi (fun i => -(∑ j,M i j • ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1)))
  let Q : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E :=
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E) A
  let b := fun x => A (fderiv ℝ U x)
  let D := fun x => Q (fderiv ℝ (fderiv ℝ U) x)
  let D₂ := fun x => Q.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ U)) x)
  have hU₁ : ContDiff ℝ 2 (fderiv ℝ U) := (contDiff_succ_iff_fderiv (n := 2)).mp hU |>.2.2
  have hU₂ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ U)) := (contDiff_succ_iff_fderiv (n := 1)).mp hU₁ |>.2.2
  have hd x : HasFDerivAt b (D x) x :=
    A.hasFDerivAt.comp x ((hU₁.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
  have hd₂ x : HasFDerivAt D (D₂ x) x :=
    Q.hasFDerivAt.comp x ((hU₂.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
  have hc : Continuous D₂ := continuous_const.clm_comp (hU₂.continuous_fderiv (by norm_num))
  let L : ℝ≥0 := ⟨‖Q‖*(A₂:ℝ)+1,by positivity⟩
  let C : ℝ≥0 := ⟨‖Q‖*(A₃:ℝ),by positivity⟩
  have hDb x : ‖D x‖≤(L:ℝ) := by
    exact ((Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h₂ x) (norm_nonneg Q))).trans
      (le_add_of_nonneg_right zero_le_one)
  have hD₂b x : ‖D₂ x‖≤(C:ℝ) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (h₃ x) (norm_nonneg Q))
  have hDC : LipschitzWith C D := by
    apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hd₂ x).differentiableAt)
    intro x
    rw [(hd₂ x).fderiv]
    exact_mod_cast hD₂b x
  have hDU : LipschitzWith A₂ (fderiv ℝ U) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hU₁.differentiable (by norm_num))
    intro x
    exact_mod_cast h₂ x
  obtain ⟨Cg,hCg,hg⟩ := lipschitz_linear_growth (fderiv ℝ U) A₂ hDU
  refine ⟨b,D,D₂,C,L,Cg,?_,hd,hd₂,hc,hDC,by change (0:ℝ)<‖Q‖*(A₂:ℝ)+1; positivity,hDb,hCg,?_⟩
  · intro x i
    change (-(∑ j,M i j • ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1))) (fderiv ℝ U x)=_
    simp only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.apply_apply,smul_eq_mul]
  · intro i x
    have he : ‖(Pi.single i 1 : Fin d → ℝ)‖≤1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
      intro j
      by_cases h : j=i <;> simp [h]
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ U x).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans (by simpa only [mul_one] using hg x))

end Asakura.Chapter8
