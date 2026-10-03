import Chapter7FiniteClockPaths
import Chapter2WrittenGridStopping

open Set Filter
open scoped Topology
namespace Asakura.Chapter7
open Asakura.Chapter2Written
set_option maxHeartbeats 1600000

/-- Exercise 7.1: all eight assertions on the book's actual finite-or-infinite
time interval. F at T records F_*; its value is the supremum of the original
half-open clock. Endpoint removal is proved separately, not assumed.
The two assertions concerning continuous clocks retain that extra hypothesis. -/
theorem inverse_clock_exercise_written
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → EReal) (hF : Monotone F) (hzero : F ⊥ = 0)
    (hr : ∀ t,ContinuousWithinAt F (Ici t) t)
    (hend : F ⊤ = sSup (F '' Iio ⊤))
    (s : EReal) (hs0 : 0 ≤ s) (hs : s < F ⊤) :
    (sInf {t | s ≤ F t} < (⊤ : ClosedTime T)) ∧
    (sInf {t | s < F t} < (⊤ : ClosedTime T)) ∧
    (sSup {t | F t < s} = sInf {t | s ≤ F t}) ∧
    (sSup {t | F t ≤ s} = sInf {t | s < F t}) ∧
    ContinuousWithinAt (fun r => sInf {t | r ≤ F t}) (Iic s) s ∧
    ContinuousWithinAt (fun r => sInf {t | r < F t}) (Ici s) s ∧
    Tendsto (fun r => sInf {t | r ≤ F t}) (𝓝[>] s) (𝓝 (sInf {t | s < F t})) ∧
    (∀ t,F t < s ↔ t < sInf {u | s ≤ F u}) ∧
    (ContinuousOn F (Iio ⊤) →
      F (sInf {t | s ≤ F t}) = s ∧ F (sInf {t | s < F t}) = s) ∧
    (ContinuousOn F (Iio ⊤) → ∀ φ : ClosedTime T → ℝ,
      ContinuousOn φ (Iio ⊤) →
      (∀ a b,a < ⊤ → b < ⊤ → F a = F b → φ a = φ b) →
      ContinuousAt (fun r => φ (sInf {t | r ≤ F t})) s ∧
      ∀ t,t < ⊤ → F t < F ⊤ → φ (sInf {u | F t ≤ F u}) = φ t) := by
  have ht := generalized_inverse_before_terminal F hend s hs
  have hcont := generalized_inverse_one_sided_continuity F hF s
  refine ⟨ht.1,ht.2,sup_lt_eq_inf_ge F hF s,sup_le_eq_inf_gt F hF s,
    hcont.1,hcont.2,weak_inverse_right_limit F s,?_,?_,?_⟩
  · exact fun t => right_continuous_inverse_event F hF hr s ⟨⊤,hs.le⟩ t
  · exact fun hc => continuous_clock_inverse_levels F hF hc hend s (by simpa only [hzero] using hs0) hs
  · intro hc φ hφ hflat
    exact ⟨finite_clock_path_continuity F hF hc hend φ hφ hflat s (by simpa only [hzero] using hs0) hs,
      fun t ht hft => finite_clock_path_recovery F hF hc hend φ hflat t ht hft⟩

end Asakura.Chapter7
