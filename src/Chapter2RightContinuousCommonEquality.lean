import Chapter2CommonTimeEquality
import Mathlib.Topology.Instances.Rat

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Fixed-time equality of right-continuous processes becomes one common
null-set equality on a finite interval. A separate endpoint equality is kept. -/
theorem right_continuous_common_equality
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (b : ℝ) (hb : 0 ≤ b)
    (X Y : ℝ → Ω → ℝ)
    (hX : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → t < b → ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (hY : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → t < b → ContinuousWithinAt (fun s => Y s ω) (Ici t) t)
    (he : ∀ t, t ∈ Icc 0 b → X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ∀ t, t ∈ Icc 0 b → X t ω = Y t ω := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, (q:ℝ) ∈ Icc 0 b → X q ω = Y q ω := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : (q:ℝ) ∈ Icc 0 b
    · exact (he q hq).mono (fun ω h _ => h)
    · exact ae_of_all _ (fun ω h => False.elim (hq h))
  filter_upwards [hX,hY,hq,he b ⟨hb,le_rfl⟩] with ω hx hy hq hbe
  intro t ht
  rcases ht.2.eq_or_lt with rfl | htb
  · exact hbe
  have hpos (n : ℕ) : 0 < (1 / ((n:ℝ)+1)) := by positivity
  have hlt (n : ℕ) : t < min b (t+1/((n:ℝ)+1)) := lt_min htb (lt_add_of_pos_right t (hpos n))
  choose q hqt htq using fun n : ℕ => exists_rat_btwn (hlt n)
  have hlim : Tendsto (fun n => (q n:ℝ)) atTop (𝓝 t) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n : ℕ => t+1/((n:ℝ)+1)) atTop (𝓝 t) from by
        simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      (fun n => (hqt n).le) (fun n => (htq n).le.trans (min_le_right _ _))
  have hw : Tendsto (fun n => (q n:ℝ)) atTop (𝓝[Ici t] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim,Filter.Eventually.of_forall (fun n => (hqt n).le)⟩
  have heq : (fun n => X (q n) ω) = (fun n => Y (q n) ω) := by
    funext n
    exact hq (q n) ⟨ht.1.trans (hqt n).le,(htq n).le.trans (min_le_left _ _)⟩
  have hxlim := (hx t ht.1 htb).tendsto.comp hw
  have hylim := (hy t ht.1 htb).tendsto.comp hw
  change Tendsto (fun n => X (q n) ω) atTop (𝓝 (X t ω)) at hxlim
  rw [heq] at hxlim
  exact tendsto_nhds_unique hxlim hylim

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.right_continuous_common_equality
