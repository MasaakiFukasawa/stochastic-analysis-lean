import Chapter8TransportMap
import FullAuditLangevinContraction

open MeasureTheory
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 600000

/-- Invariance and contraction in a quadratic coordinate norm imply geometric
convergence in the original norm, with the explicit norm-comparison constant. -/
theorem invariant_coordinate_convergence {E G Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] [MeasurableSpace Ω]
    (A : E ≃L[ℝ] G) (P : Measure Ω) [IsProbabilityMeasure P]
    (μ π : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (X : E → Ω → E) (hX : Measurable (Function.uncurry X))
    (hμ : MemLp (fun x : E => x) 2 μ) (hπ : MemLp (fun x : E => x) 2 π)
    (hXt : MemLp (fun x : E => x) 2 (flowLaw μ P X))
    (hinv : flowLaw π P X=π) (r t : ℝ)
    (hc : transportDistance ((flowLaw μ P X).map A) ((flowLaw π P X).map A) ≤
      Real.exp (-r*t)*transportDistance (μ.map A) (π.map A)) :
    transportDistance (flowLaw μ P X) π ≤
      ((‖A.symm.toContinuousLinearMap‖+1)*(‖A.toContinuousLinearMap‖+1))*
        Real.exp (-r*t)*transportDistance μ π := by
  haveI : IsProbabilityMeasure (flowLaw μ P X) := by
    change IsProbabilityMeasure ((μ.prod P).map (Function.uncurry X))
    exact (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr inferInstance
  have hm (ν : Measure E) (hv : MemLp (fun x : E => x) 2 ν) :
      MemLp (fun y : G => y) 2 (ν.map A) := by
    apply (A.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff).mpr
    exact A.toContinuousLinearMap.comp_memLp' hv
  haveI : IsProbabilityMeasure (π.map A) :=
    (Measure.isProbabilityMeasure_map_iff A.continuous.measurable.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure ((flowLaw μ P X).map A) :=
    (Measure.isProbabilityMeasure_map_iff A.continuous.measurable.aemeasurable).mpr inferInstance
  haveI := quadratic_coupling_nonempty _ _ (hm _ hXt) (hm _ hπ)
  haveI := quadratic_coupling_nonempty μ π hμ hπ
  have h₁ := transport_coordinate_comparison A (flowLaw μ P X) π
  have h₂ := transport_map_bound μ π A A.continuous.measurable
    (‖A.toContinuousLinearMap‖+1) (by positivity) (fun x y => by
      rw [← map_sub]
      exact (A.toContinuousLinearMap.le_opNorm (x-y)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)))
  rw [hinv] at hc
  calc
    _ ≤ (‖A.symm.toContinuousLinearMap‖+1)*
      (Real.exp (-r*t)*transportDistance (μ.map A) (π.map A)) :=
        h₁.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ ≤ (‖A.symm.toContinuousLinearMap‖+1)*
      (Real.exp (-r*t)*((‖A.toContinuousLinearMap‖+1)*transportDistance μ π)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h₂ (Real.exp_pos _).le) (by positivity)
    _ = _ := by ring

/-- Strict contraction after an invertible coordinate change separates
invariant probability measures without any density assumption. -/
theorem invariant_coordinate_unique {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G]
    (A : E ≃L[ℝ] G) (μ π : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : MemLp (fun x : E => x) 2 μ) (hπ : MemLp (fun x : E => x) 2 π)
    (a : ℝ) (ha : a<1)
    (hc : transportDistance (μ.map A) (π.map A) ≤
      a*transportDistance (μ.map A) (π.map A)) : μ=π := by
  have hm (ν : Measure E) (hv : MemLp (fun x : E => x) 2 ν) :
      MemLp (fun y : G => y) 2 (ν.map A) := by
    apply (A.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff).mpr
    exact A.toContinuousLinearMap.comp_memLp' hv
  haveI := quadratic_coupling_nonempty μ π hμ hπ
  haveI : IsProbabilityMeasure (μ.map A) :=
    (Measure.isProbabilityMeasure_map_iff A.continuous.measurable.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure (π.map A) :=
    (Measure.isProbabilityMeasure_map_iff A.continuous.measurable.aemeasurable).mpr inferInstance
  haveI := quadratic_coupling_nonempty _ _ (hm _ hμ) (hm _ hπ)
  have hn : 0≤transportDistance (μ.map A) (π.map A) := Real.sqrt_nonneg _
  have hz : transportDistance (μ.map A) (π.map A)=0 := by nlinarith
  have hd := transport_coordinate_comparison A μ π
  rw [hz,mul_zero] at hd
  have hzero : transportDistance μ π=0 := le_antisymm hd (Real.sqrt_nonneg _)
  apply zero_transport_measures_equal μ π
  have hs := Real.sq_sqrt (transport_energy_nonnegative μ π)
  change (transportDistance μ π)^2=transportEnergy μ π at hs
  rw [hzero] at hs
  nlinarith

end Asakura.Chapter8
