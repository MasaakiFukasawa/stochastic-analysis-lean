import Chapter7ClockHalfTime

open Set
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter7

def canonicalClock (n : ℕ) : ℝ := n+1

theorem canonical_clock_properties :
    (∀ n,0<canonicalClock n) ∧ StrictMono canonicalClock ∧
    StrictMono (fun n => realTimeClamp (T := ⊤) (canonicalClock n)) ∧
    (∀ n,realTimeClamp (T := ⊤) (canonicalClock n)<⊤) ∧
    (∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (canonicalClock n)) ∧
    (∀ r : ℝ,∃ n,r≤canonicalClock n) := by
  have hp (n : ℕ) : 0<canonicalClock n := by unfold canonicalClock; positivity
  have hm : StrictMono canonicalClock := by
    intro n k hnk
    unfold canonicalClock
    have he : (n:ℝ)<(k:ℝ) := by exact_mod_cast hnk
    linarith
  have hco (r : ℝ) : ∃ n,r<canonicalClock n := by
    obtain ⟨n,hn⟩ := exists_nat_gt r
    exact ⟨n,hn.trans (by unfold canonicalClock; linarith)⟩
  refine ⟨hp,hm,?_,fun n => changed_time_finite _ (hp n).le,
    changed_time_cofinal _ (fun n => (hp n).le) hco,fun r => ?_⟩
  · intro n k hnk
    change (realTimeClamp (canonicalClock n) : EReal)<(realTimeClamp (canonicalClock k) : EReal)
    rw [real_time_clamp_eq _ (hp n).le le_top,real_time_clamp_eq _ (hp k).le le_top]
    exact_mod_cast hm hnk
  · obtain ⟨n,hn⟩ := hco r
    exact ⟨n,hn.le⟩

end Asakura.Chapter12
