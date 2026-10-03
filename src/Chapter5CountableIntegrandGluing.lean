import Chapter5ProgressivePrimitive
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Countable pasting of the interval integrands preserves progressive
measurability. The index depends only on time. -/
theorem progressive_countable_time_choice
    {Ω ι : Type*} [Preorder ι] [MeasurableSpace ι]
    (F : ι → MeasurableSpace Ω) (k : ι → ℕ) (hk : Measurable k)
    (H : ℕ → Ω × ι → ℝ)
    (hH : ∀ n,@Measurable _ _ (progressiveSpace F) inferInstance (H n)) :
    @Measurable _ _ (progressiveSpace F) inferInstance (fun z => H (k z.2) z) := by
  apply (measurable_progressive_iff F _).mpr
  intro t
  let : MeasurableSpace Ω := F t
  have hm : Measurable (fun p : (Ω × Iic t) × ℕ => H p.2 (p.1.1,p.1.2.val)) :=
    measurable_from_prod_countable_left fun n => (measurable_progressive_iff F _).mp (hH n) t
  exact hm.comp (measurable_id.prodMk (hk.comp (measurable_subtype_coe.comp measurable_snd)))

/-- On every bounded time interval only finitely many pieces occur.
This proves the required local square integrability, not just the
pointwise existence of the pasted process. -/
theorem finite_choice_memLp_two
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (k : α → ℕ) (hk : Measurable k) (N : ℕ) (hkN : ∀ᵐ a ∂μ,k a ≤ N)
    (H : ℕ → α → ℝ) (hm : ∀ n,Measurable (H n))
    (hi : ∀ n,n ≤ N → MemLp (H n) 2 μ) :
    MemLp (fun a => H (k a) a) 2 μ := by
  have hm' : Measurable (fun p : α × ℕ => H p.2 p.1) := measurable_from_prod_countable_left hm
  have hs : MemLp (fun a => ∑ n ∈ Finset.range (N+1), ‖H n a‖) 2 μ := by
    apply memLp_finsetSum
    intro n hn
    exact (hi n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).norm
  apply hs.mono' (hm'.comp (measurable_id.prodMk hk)).aestronglyMeasurable
  filter_upwards [hkN] with a ha
  exact Finset.single_le_sum (fun n _ => norm_nonneg (H n a))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))

end Asakura.Chapter5
