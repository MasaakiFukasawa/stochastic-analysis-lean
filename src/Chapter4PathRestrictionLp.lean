import Chapter4PathRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 800000

lemma restrict_real_path_memLp_exponent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {R d : ℝ} (hdR : d≤R) (Y : Ω → C(Icc (0:ℝ) R,ℝ))
    (hm : Measurable Y) (p : ℝ≥0∞) (hi : MemLp Y p P) :
    MemLp (fun w => restrictRealPath hdR (Y w)) p P := by
  apply hi.of_le_mul (c := 1) (restrict_real_path_measurable hdR Y hm).aestronglyMeasurable
  exact .of_forall (fun w => by simpa only [one_mul] using restrict_real_path_norm_le hdR (Y w))

end Asakura.Chapter4
