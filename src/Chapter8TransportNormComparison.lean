import Chapter8TransportMap

open MeasureTheory
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1000000

/-- Compare transport distances in two explicit coordinate norms using a
prescribed comparison constant, without replacing it by a dimension-dependent
bound for the coordinate representation. -/
theorem transport_between_coordinate_norms {E G K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K]
    (A : E ≃L[ℝ] G) (R : E ≃L[ℝ] K) (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun z => z) 2 μ) (hν : MemLp (fun z => z) 2 ν)
    (c : ℝ) (hc : 0<c) (hb : ∀ z,‖R z‖≤c*‖A z‖) :
    transportDistance (μ.map R) (ν.map R)≤c*transportDistance (μ.map A) (ν.map A) := by
  have hm (η : Measure E) (hη : MemLp (fun z => z) 2 η) :
      MemLp (fun z : G => z) 2 (η.map A) := by
    apply A.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff.mpr
    exact A.toContinuousLinearMap.comp_memLp' hη
  haveI : IsProbabilityMeasure (μ.map A) :=
    (Measure.isProbabilityMeasure_map_iff A.continuous.measurable.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure (ν.map A) :=
    (Measure.isProbabilityMeasure_map_iff A.continuous.measurable.aemeasurable).mpr inferInstance
  haveI := quadratic_coupling_nonempty _ _ (hm μ hμ) (hm ν hν)
  let C := A.symm.trans R
  have hC (x y : G) : ‖C x-C y‖≤c*‖x-y‖ := by
    rw [←map_sub C]
    simpa only [C,ContinuousLinearEquiv.trans_apply,A.apply_symm_apply] using hb (A.symm (x-y))
  have hh := transport_map_bound (μ.map A) (ν.map A) C C.continuous.measurable c hc hC
  have he (η : Measure E) : (η.map A).map C=η.map R := by
    rw [Measure.map_map C.continuous.measurable A.continuous.measurable]
    congr 1
    funext z
    exact congrArg R (A.symm_apply_apply z)
  rwa [he μ,he ν] at hh

end Asakura.Chapter8
