import Chapter8ObservableSecondDerivative
import Chapter8BoundedExpectationC2
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

open MeasureTheory Set
namespace Asakura.Chapter8
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- C2 regularity of the actual expectation of an observable of a smooth
additive flow. Joint continuity supplies every required measurability
hypothesis; deterministic variation bounds justify both differentiations. -/
theorem smooth_flow_expectation_C2 {E N Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace N] [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → N) (hV : Measurable V)
    (S : E × N → E) (J : E × N → E →L[ℝ] E) (K : E × N → E →L[ℝ] E →L[ℝ] E)
    (hcS : Continuous S) (hcJ : Continuous J) (hcK : Continuous K)
    (hS : ∀ x w,HasFDerivAt (fun z => S (z,w)) (J (x,w)) x)
    (hJ : ∀ x w,HasFDerivAt (fun z => J (z,w)) (K (x,w)) x)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hJb : ∀ p,‖J p‖ ≤ A) (hKb : ∀ p,‖K p‖ ≤ B)
    (f : E → ℝ) (Df : E → E →L[ℝ] ℝ) (D₂f : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ z,HasFDerivAt f (Df z) z) (hDf : ∀ z,HasFDerivAt Df (D₂f z) z)
    (hcD₂f : Continuous D₂f) (B₀ B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hfb : ∀ z,‖f z‖ ≤ B₀) (hDfb : ∀ z,‖Df z‖ ≤ B₁) (hD₂fb : ∀ z,‖D₂f z‖ ≤ B₂) :
    ContDiff ℝ 2 (fun x => ∫ ω,f (S (x,V ω)) ∂P) ∧
      (∀ x,‖fderiv ℝ (fun z => ∫ ω,f (S (z,V ω)) ∂P) x‖ ≤ B₁*A) ∧
      ∀ x,‖fderiv ℝ (fderiv ℝ (fun z => ∫ ω,f (S (z,V ω)) ∂P)) x‖ ≤ B₁*B+B₂*A^2 := by
  borelize (E →L[ℝ] ℝ)
  borelize (E →L[ℝ] E →L[ℝ] ℝ)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun z => (hf z).continuousAt)
  have hDfc : Continuous Df := continuous_iff_continuousAt.mpr (fun z => (hDf z).continuousAt)
  let Q := fun p : E × N => (Df (S p)).comp (J p)
  let R := fun p : E × N => observableSecondDerivative (Df (S p)) (D₂f (S p)) (J p) (K p)
  have hQc : Continuous Q := (hDfc.comp hcS).clm_comp hcJ
  have hRc : Continuous R := by
    exact ((continuous_const.clm_apply (hDfc.comp hcS)).clm_comp hcK).add
      ((continuous_const.clm_apply hcJ).clm_comp ((hcD₂f.comp hcS).clm_comp hcJ))
  have hQb p : ‖Q p‖ ≤ B₁*A :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hDfb _) (hJb p) (norm_nonneg _) hB₁)
  have hRb p : ‖R p‖ ≤ B₁*B+B₂*A^2 := by
    apply (observable_second_derivative_norm _ _ _ _).trans
    apply add_le_add
    · exact mul_le_mul (hDfb _) (hKb p) (norm_nonneg _) hB₁
    · exact mul_le_mul (hD₂fb _) (pow_le_pow_left₀ (norm_nonneg _) (hJb p) 2) (sq_nonneg _) hB₂
  have hFm x : AEStronglyMeasurable (fun ω => f (S (x,V ω))) P :=
    ((hfc.comp hcS).measurable.comp (measurable_const.prodMk hV)).aestronglyMeasurable
  have hQm x : AEStronglyMeasurable (fun ω => Q (x,V ω)) P :=
    (hQc.measurable.comp (measurable_const.prodMk hV)).aestronglyMeasurable
  have hRm x : AEStronglyMeasurable (fun ω => R (x,V ω)) P :=
    (hRc.measurable.comp (measurable_const.prodMk hV)).aestronglyMeasurable
  have hd x ω := observable_composition_derivatives (fun z => S (z,V ω)) (fun z => J (z,V ω)) x
    (K (x,V ω)) (hS x (V ω)) (hJ x (V ω)) f Df (D₂f (S (x,V ω))) (hf _) (hDf _)
  have hh := bounded_expectation_C2 P (fun x ω => f (S (x,V ω))) (fun x ω => Q (x,V ω)) (fun x ω => R (x,V ω))
    hFm hQm hRm B₀ (B₁*A) (B₁*B+B₂*A^2)
    (fun x => ae_of_all _ (fun ω => hfb _))
    (ae_of_all _ (fun ω x => hQb (x,V ω)))
    (ae_of_all _ (fun ω x => hRb (x,V ω)))
    (ae_of_all _ (fun ω x => (hd x ω).1))
    (ae_of_all _ (fun ω x => (hd x ω).2))
    (ae_of_all _ (fun ω => hRc.comp (continuous_id.prodMk continuous_const)))
  exact ⟨hh.1,hh.2.2.2.1,hh.2.2.2.2⟩

end Asakura.Chapter8
