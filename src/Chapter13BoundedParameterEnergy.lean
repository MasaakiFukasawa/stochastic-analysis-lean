import Chapter13FubiniEnergy

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 1800000

/-- The manuscript's pathwise local boundedness on each finite rectangle
supplies the pathwise parameter/time L2 input, without a deterministic or
integrable random bound. -/
theorem bounded_parameter_time_energy {E:Type*} [MeasurableSpace E]
    (μ:Measure E) [IsFiniteMeasure μ] (R:ℝ) (H:E × ℝ → ℝ) (hm:Measurable H)
    (K:ℝ) (hK:0≤K) (hb:∀x r,r∈Icc 0 R → |H (x,r)|≤K) :
    Integrable (fun z => H z^2) (μ.prod (volume.restrict (Ioc 0 R))) := by
  apply (integrable_const (K^2)).mono' (hm.pow_const 2).aestronglyMeasurable
  have hs:∀ᵐz:E × ℝ∂μ.prod (volume.restrict (Ioc 0 R)),z.2∈Ioc 0 R :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hs] with z hz
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (hb z.1 z.2 ⟨hz.1.le,hz.2⟩)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.bounded_parameter_time_energy
