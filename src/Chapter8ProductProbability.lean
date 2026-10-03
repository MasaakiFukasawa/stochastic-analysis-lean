import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Filter Set
namespace Asakura.Chapter8

/-- Adding an independent initial coordinate does not change convergence
in probability of observations depending only on the original sample. -/
theorem probability_from_product {Ω A I : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) (ν : Measure A) [IsProbabilityMeasure ν] [SFinite P]
    (X : I → Ω → ℝ) (hX : ∀ i,Measurable (X i)) (l : Filter I) (c : ℝ)
    (h : TendstoInMeasure (ν.prod P) (fun i z => X i z.2) l (fun _ => c)) :
    TendstoInMeasure P X l (fun _ => c) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  have hh := tendstoInMeasure_iff_dist.mp h ε hε
  have he i : (ν.prod P) {z | ε≤dist (X i z.2) c}=P {w | ε≤dist (X i w) c} := by
    have hm : MeasurableSet {w | ε≤dist (X i w) c} := measurableSet_le measurable_const ((hX i).dist measurable_const)
    change (ν.prod P) (Prod.snd ⁻¹' {w | ε≤dist (X i w) c})=_
    rw [←Measure.map_apply measurable_snd hm,Measure.map_snd_prod,measure_univ,one_smul]
  simpa only [he] using hh
end Asakura.Chapter8
