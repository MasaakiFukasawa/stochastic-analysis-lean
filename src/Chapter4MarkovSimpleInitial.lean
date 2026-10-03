import Chapter4PredictableBrownianIncrement
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The finite-valued-initial-state step in the Markov proof. The future
noise law and its independence are used explicitly, via conditional
expectation on each atom of the initial-state partition. -/
theorem independent_noise_simple_initial_condExp
    {Ω E ι : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (Z : Ω → E) (hZ : Measurable[m] Z) (ν : Measure E) (hlaw : HasLaw Z ν P)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) G P)
    (η : Ω → ι) (hη : Measurable[G] η)
    (f : ι → E → ℝ) (hf : ∀ i,Measurable (f i))
    (C : ℝ) (hb : ∀ i x,‖f i x‖≤C) :
    P[(fun w => f (η w) (Z w)) | G]=ᵐ[P] fun w => ∫ z,f (η w) z ∂ν := by
  classical
  let A := fun i => {w | η w=i}
  let H := fun i => (A i).indicator (fun w => f i (Z w))
  have hA i : MeasurableSet[G] (A i) := hη (measurableSet_singleton i)
  have hi i : Integrable (fun w => f i (Z w)) P := (integrable_const C).mono'
    ((hf i).comp hZ).aestronglyMeasurable (Filter.Eventually.of_forall (fun w => hb i (Z w)))
  have hHi i : Integrable (H i) P := (hi i).indicator (hG _ (hA i))
  have hZi : Measurable[MeasurableSpace.comap Z inferInstance] Z := measurable_iff_comap_le.mpr le_rfl
  have hbase i : P[(fun w => f i (Z w)) | G]=ᵐ[P] fun _ => ∫ z,f i z ∂ν := by
    have he := condExp_indep_eq hZ.comap_le hG ((hf i).comp hZi).stronglyMeasurable hind
    have hl := hlaw.integral_comp (hf i).aestronglyMeasurable
    exact he.trans (Filter.Eventually.of_forall (fun _ => hl))
  have hcond i : P[H i | G]=ᵐ[P] (A i).indicator (fun _ => ∫ z,f i z ∂ν) := by
    filter_upwards [condExp_indicator (hi i) (hA i),hbase i] with w hw hw'
    change P[(A i).indicator (fun w => f i (Z w)) | G] w=_
    rw [hw]
    by_cases hwa : w∈A i <;> simp only [indicator,hwa,if_true,if_false,hw']
  have hsplit : (fun w => f (η w) (Z w))=∑ i,H i := by
    funext w
    simp only [Finset.sum_apply,H,A,indicator,mem_setOf_eq]
    simp
  rw [hsplit]
  filter_upwards [condExp_finsetSum (s:=Finset.univ) (f:=H) (fun i _ => hHi i) G,
    ae_all_iff.mpr hcond] with w hw hc
  rw [hw]
  simp only [Finset.sum_apply,hc,A,indicator,mem_setOf_eq]
  simp

end Asakura.Chapter4
