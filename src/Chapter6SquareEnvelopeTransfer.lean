import Chapter6DensityL2Transfer

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
set_option backward.isDefEq.respectTransparency false

/-- The L2(P) path bound becomes an L1(Q) path bound using the proved
second moment of the density. -/
theorem square_envelope_density_transfer {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) (d : Ω → ℝ≥0) (hd : Measurable d)
    (hQ : Q=P.withDensity (fun w => (d w:ℝ≥0∞)))
    (hd2 : MemLp (fun w => (d w:ℝ)) 2 P)
    (U : Ω → ℝ) (hU : Integrable U P) (hUp : ∀ w,0≤U w) :
    Integrable (fun w => Real.sqrt (U w)) Q := by
  have hm : AEStronglyMeasurable (fun w => Real.sqrt (U w)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hU.aestronglyMeasurable
  have h2 : MemLp (fun w => Real.sqrt (U w)) 2 P := by
    apply (memLp_two_iff_integrable_sq hm).mpr
    simpa only [Real.sq_sqrt (hUp _)] using hU
  exact square_integrable_density_transfer P Q d hd hQ hd2 _ h2

end Asakura.Chapter6
