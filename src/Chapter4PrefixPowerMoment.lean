import Chapter4PrefixMoment
import Chapter4PowerGrowth

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 1200000

/-- Continuity of the stopped p-th moment follows from Lp path domination. -/
theorem prefix_power_moment_continuous {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℝ} (hd : 0≤d) (Y : Ω → C(Icc (0:ℝ) d,ℝ))
    (hm : Measurable Y) (p : ℝ) (hp : 0<p) (hi : MemLp Y (ENNReal.ofReal p) P) :
    Continuous (fun t : ℝ => ∫ w,‖prefixPath hd (Y w) t‖^p ∂P) := by
  apply continuous_of_dominated (bound := fun w => ‖Y w‖^p)
  · intro t
    exact ((Real.continuous_rpow_const hp.le).measurable.comp (prefix_path_measurable hd Y hm t).norm).aestronglyMeasurable
  · intro t
    exact .of_forall (fun w => by
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
      exact Real.rpow_le_rpow (norm_nonneg _) (prefix_path_norm_le hd (Y w) t) hp.le)
  · simpa only [ENNReal.toReal_ofReal hp.le] using hi.integrable_norm_rpow
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top
  · exact .of_forall (fun w => (Real.continuous_rpow_const hp.le).comp (prefix_path_time_continuous hd (Y w)).norm)

/-- The level-stopped path has a finite p moment because its supremum is
bounded by the initial magnitude plus the stopping level. -/
theorem stopped_path_memLp_of_initial_bound
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) [IsFiniteMeasure P] (Y : Ω → E) (hm : AEStronglyMeasurable Y P)
    (ξ : Ω → ℝ) (p : ℝ≥0∞) (hi : MemLp ξ p P) (K : ℝ) (hK : 0≤K)
    (hb : ∀ᵐ w ∂P,‖Y w‖≤|ξ w|+K) : MemLp Y p P := by
  have hh : MemLp (fun w => |ξ w|+K) p P := by
    exact MemLp.add (f := fun w => |ξ w|) (g := fun _ => K) hi.norm (memLp_const K)
  apply hh.of_le_mul (c := 1) hm
  filter_upwards [hb] with w hw
  simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (abs_nonneg _) hK)] using hw

end Asakura.Chapter4
