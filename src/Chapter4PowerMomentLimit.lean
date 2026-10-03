import Chapter4PicardFatou
import Chapter4PrefixPowerMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 1200000

/-- The final localization limit: a uniform p-moment bound for level-stopped
paths proves the full path's p-integrability. -/
theorem power_moment_limit
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (Y : Ω → E) (hm : AEStronglyMeasurable Y P)
    (Z : ℕ → Ω → E) (p : ℝ) (hp : 0<p)
    (hi : ∀ n,MemLp (Z n) (ENNReal.ofReal p) P)
    (A : ℝ) (hA : 0≤A) (hb : ∀ n,(∫ w,‖Z n w‖^p ∂P)≤A)
    (he : ∀ᵐ w ∂P,Tendsto (fun n => Z n w) atTop (𝓝 (Y w))) :
    MemLp Y (ENNReal.ofReal p) P := by
  have hz n : eLpNorm (Z n) (ENNReal.ofReal p) P≤ENNReal.ofReal (A^(p⁻¹)) := by
    rw [(hi n).eLpNorm_eq_integral_rpow_norm (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp.le]
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow (integral_nonneg (fun w => Real.rpow_nonneg (norm_nonneg _) _)) (hb n) (inv_nonneg.mpr hp.le)
  have hh := Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hi n).aestronglyMeasurable)
    Y hm he (p := ENNReal.ofReal p)
  have hh' : Filter.liminf (fun n => eLpNorm (Z n) (ENNReal.ofReal p) P) atTop≤ENNReal.ofReal (A^(p⁻¹)) :=
    liminf_le_of_frequently_le' (Filter.Eventually.frequently (Filter.Eventually.of_forall hz))
  exact (hh.trans hh').trans_lt ENNReal.ofReal_lt_top

end Asakura.Chapter4
