import Chapter7RightFiltrationLimit
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000

/-- Strict sublevel events measurable just after s give weak sublevel events
in the intersection of the future sigma algebras. This supplies the stopping
times in the right-continuous DDS filtration. -/
theorem right_filtration_clock_stopping
    {Ω : Type*} (H : ℝ → MeasurableSpace Ω) (hm : Monotone H)
    (σ : Ω → ℝ) (hσ : ∀ r,MeasurableSet[H r] {w | σ w < r}) (s : ℝ) :
    MeasurableSet[⨅ r : Ioi s,H r.val] {w | σ w ≤ s} := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro r
  let u := fun n : ℕ => s+(r.val-s)/(n+1:ℝ)
  have hu n : s < u n ∧ u n ≤ r.val := by
    have hd : 0 < (n+1:ℝ) := by positivity
    have hone : (1:ℝ) ≤ n+1 := by have hh := Nat.cast_nonneg (α := ℝ) n; linarith
    have hdiv := div_le_self (sub_nonneg.mpr r.property.le) hone
    constructor
    · exact lt_add_of_pos_right s (div_pos (sub_pos.mpr r.property) hd)
    · dsimp [u]; linarith
  have hlim : Tendsto u atTop (𝓝 s) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r.val-s)
    convert (tendsto_const_nhds (x := s)).add hh using 1 <;> simp [u,div_eq_mul_inv]
  have he : {w | σ w ≤ s} = ⋂ n,{w | σ w < u n} := by
    ext w
    simp only [mem_setOf_eq,mem_iInter]
    constructor
    · exact fun h n => h.trans_lt (hu n).1
    · intro h
      exact ge_of_tendsto' hlim (fun n => (h n).le)
  rw [he]
  exact MeasurableSet.iInter (fun n => hm (hu n).2 _ (hσ (u n)))

/-- The right-continuous hull is a filtration, and contains each original
sigma algebra. -/
theorem right_filtration_mono
    {Ω : Type*} (H : ℝ → MeasurableSpace Ω) (hm : Monotone H) :
    Monotone (fun s => ⨅ r : Ioi s,H r.val) ∧ ∀ s,H s ≤ ⨅ r : Ioi s,H r.val := by
  constructor
  · intro s t hst
    apply le_iInf
    intro r
    exact iInf_le_of_le ⟨r.val,hst.trans_lt r.property⟩ le_rfl
  · intro s
    exact le_iInf (fun r => hm r.property.le)

/-- A decreasing sequence of times approaching s computes the full future
intersection, not a smaller or larger sigma algebra. -/
theorem right_filtration_countable_intersection
    {Ω : Type*} (H : ℝ → MeasurableSpace Ω) (hm : Monotone H)
    (s : ℝ) (u : ℕ → ℝ) (hu : ∀ n,s < u n) (hl : Tendsto u atTop (𝓝 s)) :
    (⨅ n,H (u n)) = ⨅ r : Ioi s,H r.val := by
  apply le_antisymm
  · apply le_iInf
    intro r
    obtain ⟨n,hn⟩ := (hl.eventually (gt_mem_nhds r.property)).exists
    exact (iInf_le (fun n => H (u n)) n).trans (hm hn.le)
  · exact le_iInf (fun n => iInf_le_of_le ⟨u n,hu n⟩ le_rfl)

end Asakura.Chapter7
