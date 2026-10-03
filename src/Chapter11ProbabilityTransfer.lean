import Chapter11CommonIntegralLimit
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
set_option maxHeartbeats 1200000

lemma nonnegative_probability_transfer {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure Q] (hQP : Q ≪ P)
    (E : ℕ → Ω → ℝ) (hE : ∀ n,Measurable (E n)) (hpos : ∀ n w,0≤E n w)
    (hp : ∀ ε>0,Tendsto (fun n => P {w | ε≤E n w}) atTop (𝓝 0)) :
    ∀ ε>0,Tendsto (fun n => Q {w | ε≤E n w}) atTop (𝓝 0) := by
  have hlim : TendstoInMeasure P E atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm]
    simpa only [sub_zero,Real.norm_eq_abs,abs_of_nonneg (hpos _ _)] using hp
  have hq := Asakura.Chapter8.probability_absolutely_continuous P Q hQP E (fun _ => 0)
    (fun n => (hE n).aestronglyMeasurable) hlim
  rw [tendstoInMeasure_iff_norm] at hq
  simpa only [sub_zero,Real.norm_eq_abs,abs_of_nonneg (hpos _ _)] using hq

lemma bounded_coefficient_transfer {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) (hQP : Q ≪ P) (G : Ω → ℝ) (hGm : Measurable G)
    (hG : MemLp G ∞ P) : MemLp G ∞ Q := by
  change eLpNorm G ∞ Q<∞
  rw [eLpNorm_exponent_top hGm.aestronglyMeasurable]
  apply lt_of_le_of_lt (eLpNormEssSup_le_of_ae_enorm_bound (hQP.ae_le (ae_le_eLpNormEssSup (f:=G) (μ:=P))))
  simpa only [eLpNorm_exponent_top hG.aestronglyMeasurable] using hG.eLpNorm_lt_top

end Asakura.Chapter11
