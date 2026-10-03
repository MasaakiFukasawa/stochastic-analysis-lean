import Chapter3VectorOscillationStep
import Mathlib.Topology.Order.MonotoneConvergence

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1200000

/-- The actual cofinality argument for oscillation partitions. Continuity
is needed only strictly before the terminal time, as in the manuscript. -/
theorem vector_oscillation_partition_cofinal
    {E : Type*} [NormedAddCommGroup E]
    {ι : Type*} [CompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (X : ι → E) (hX : ∀ t, t < ⊤ → ContinuousAt X t)
    (τ c : ℕ → ι) (hτ : Monotone τ) (hc : Monotone c)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (δ : ℝ) (hδ : 0 < δ)
    (hinc : ∀ n, τ (n+1) < c n → δ ≤ ‖X (τ (n+1))-X (τ n)‖) :
    ∀ t, t < ⊤ → ∃ n, t < τ n := by
  intro t ht
  by_contra hn
  have hbound : ∀ n, τ n ≤ t := by
    intro n
    exact le_of_not_gt (fun h => hn ⟨n,h⟩)
  let s := ⨆ n, τ n
  have hst : s ≤ t := iSup_le hbound
  have hs : s < ⊤ := hst.trans_lt ht
  obtain ⟨N,hN⟩ := hcc s hs
  have hl : Tendsto τ atTop (𝓝 s) := tendsto_atTop_iSup hτ
  have hl' : Tendsto (fun n => τ (n+1)) atTop (𝓝 s) :=
    (tendsto_add_atTop_iff_nat 1).mpr hl
  have hz : Tendsto (fun n => ‖X (τ (n+1))-X (τ n)‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,Function.comp_def] using (((hX s hs).tendsto.comp hl').sub ((hX s hs).tendsto.comp hl)).norm
  have he : ∀ᶠ n in atTop, δ ≤ ‖X (τ (n+1))-X (τ n)‖ := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hinc n ((le_iSup τ (n+1)).trans_lt (hN.trans_le (hc hn)))
  exact (not_le_of_gt hδ) (ge_of_tendsto hz he)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.vector_oscillation_partition_cofinal
