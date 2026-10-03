import Chapter2HalfLineLocalization
import Chapter2ItoCovarianceCharacterization

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete

lemma changed_time_real (r : ℝ) (hr : 0 ≤ r) :
    (halfTimeReal (realTimeClamp (T := (⊤:EReal)) r) : ℝ) = r := by
  change (realTimeClamp (T := (⊤:EReal)) r : EReal).toReal = r
  rw [real_time_clamp_eq r hr le_top,EReal.toReal_coe]

lemma changed_time_finite (r : ℝ) (hr : 0 ≤ r) :
    realTimeClamp (T := (⊤:EReal)) r < ⊤ := by
  change (realTimeClamp (T := (⊤:EReal)) r : EReal) < ⊤
  rw [real_time_clamp_eq r hr le_top]
  exact EReal.coe_lt_top r

lemma changed_time_min_real (r : ℝ) (hr : 0 ≤ r) (t : HalfClosedTime) (ht : t < ⊤) :
    (halfTimeReal (min (realTimeClamp r) t) : ℝ) = min r (halfTimeReal t : ℝ) := by
  obtain ⟨d,hd,hdT,rfl⟩ := finite_closed_time_real t ht
  rw [← real_time_clamp_mono.map_min,changed_time_real _ (le_min hr hd),changed_time_real d hd]

lemma changed_time_cofinal
    (σ : ℕ → ℝ) (hn : ∀ n,0 ≤ σ n) (hc : ∀ r : ℝ,∃ n,r < σ n) :
    ∀ t : HalfClosedTime,t < ⊤ → ∃ n,t < realTimeClamp (σ n) := by
  intro t ht
  obtain ⟨d,hd,hdT,rfl⟩ := finite_closed_time_real t ht
  obtain ⟨n,hn'⟩ := hc d
  refine ⟨n,?_⟩
  change (realTimeClamp d : EReal) < (realTimeClamp (σ n) : EReal)
  rw [real_time_clamp_eq d hd le_top,real_time_clamp_eq _ (hn n) le_top]
  exact_mod_cast hn'

lemma changed_time_coordinate_continuousAt (t : HalfClosedTime) (ht : t < ⊤) :
    ContinuousAt (fun s : HalfClosedTime => (halfTimeReal s : ℝ)) t := by
  exact (EReal.tendsto_toReal (ne_of_lt ht)
    (ne_of_gt ((EReal.bot_lt_coe 0).trans_le t.property.1))).comp
    continuous_subtype_val.continuousAt

lemma changed_time_le_iff (r : ℝ) (hr : 0 ≤ r) (t : HalfClosedTime) (ht : t < ⊤) :
    realTimeClamp r ≤ t ↔ r ≤ (halfTimeReal t : ℝ) := by
  obtain ⟨d,hd,hdT,rfl⟩ := finite_closed_time_real t ht
  rw [changed_time_real d hd]
  change (realTimeClamp r : EReal) ≤ (realTimeClamp d : EReal) ↔ r ≤ d
  rw [real_time_clamp_eq r hr le_top,real_time_clamp_eq d hd le_top,EReal.coe_le_coe_iff]

end Asakura.Chapter7
