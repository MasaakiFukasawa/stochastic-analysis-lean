import Chapter8OUStationary
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- An unchanged coordinate retains any probability distribution,
independently of a stationary first coordinate. -/
theorem frozen_coordinate_invariance {A D Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace Ω]
    (μ : Measure A) (ν : Measure D) (P : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    (F : A × Ω → A) (hF : Measurable F) (hi : (μ.prod P).map F=μ) :
    ((μ.prod ν).prod P).map (fun z => (F (z.1.1,z.2),z.1.2))=μ.prod ν := by
  have hp := ((measurePreserving_prodAssoc μ P ν).symm MeasurableEquiv.prodAssoc).comp
    (((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := P))).comp
      (measurePreserving_prodAssoc μ ν P))
  have hf : MeasurePreserving F (μ.prod P) μ := ⟨hF,hi⟩
  exact ((hf.prod (MeasurePreserving.id ν)).comp hp).map_eq

/-- The explicit OU transition preserves its Gaussian first coordinate
and every law of the frozen second coordinate, with no moment assumption on it. -/
theorem frozen_ou_product_invariant (κ σ : ℝ) (hκ : 0<κ) (t : ℝ≥0)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (((gaussianReal 0 (ouStationaryVariance κ σ hκ)).prod ν).prod
      (gaussianReal 0 (Asakura.FullAudit.ouVariance κ σ hκ t))).map
        (fun z => (Real.exp (-κ*(t:ℝ))*z.1.1+z.2,z.1.2))=
      (gaussianReal 0 (ouStationaryVariance κ σ hκ)).prod ν := by
  let μ := gaussianReal 0 (ouStationaryVariance κ σ hκ)
  let P := gaussianReal 0 (Asakura.FullAudit.ouVariance κ σ hκ t)
  apply frozen_coordinate_invariance μ ν P (fun z => Real.exp (-κ*(t:ℝ))*z.1+z.2) (by fun_prop)
  have hh := ou_stationary_gaussian κ σ hκ t
  change (μ.map (fun x => Real.exp (-κ*(t:ℝ))*x)) ∗ P=μ at hh
  have he := Measure.map_prod_map μ P
    (show Measurable (fun x : ℝ => Real.exp (-κ*(t:ℝ))*x) by fun_prop) measurable_id
  rw [Measure.map_id] at he
  rw [Measure.conv,he,Measure.map_map (by fun_prop) (by fun_prop)] at hh
  exact hh

theorem frozen_coordinate_nonunique (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ.prod (Measure.dirac (0:ℝ))≠μ.prod (Measure.dirac (1:ℝ)) := by
  intro h
  have hh := congrArg (fun η : Measure (ℝ × ℝ) => η.map Prod.snd) h
  simp only [Measure.map_snd_prod,measure_univ,one_smul] at hh
  have hz := congrArg (fun η : Measure ℝ => η {0}) hh
  simp at hz

end Asakura.Chapter8
