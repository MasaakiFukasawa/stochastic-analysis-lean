import FullAuditLpComplete
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Countably many measurable local representatives which agree almost
everywhere on overlaps glue after one common measurable null-set removal.
No sigma-finiteness or finite mass of the covering sets is required. -/
theorem measurable_local_ae_pasting
    {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (K : ℕ → Set S) (hK : ∀ n, MeasurableSet (K n))
    (g : ℕ → S → ℝ) (hg : ∀ n, Measurable (g n))
    (hc : ∀ i j, g i =ᵐ[μ.restrict (K i ∩ K j)] g j) :
    ∃ f : S → ℝ, Measurable f ∧ ∀ n, f =ᵐ[μ.restrict (K n)] g n := by
  classical
  let B := {x | ∀ i j, x ∈ K i ∩ K j → g i x = g j x}
  have hB : MeasurableSet B := by
    dsimp only [B]
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    exact ((hK i).inter (hK j)).imp (measurableSet_eq_fun (hg i) (hg j))
  have hBa : ∀ᵐ x ∂μ, x ∈ B := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact (ae_restrict_iff' ((hK i).inter (hK j))).mp (hc i j)
  let g' := fun n => B.indicator (g n)
  obtain ⟨f,hf,hfg⟩ := exists_measurable_piecewise K hK g' (fun n => (hg n).indicator hB) (by
    intro i j hij x hx
    by_cases hxB : x ∈ B
    · simp only [g',indicator_of_mem hxB]
      exact hxB i j hx
    · simp only [g',indicator_of_notMem hxB])
  refine ⟨f,hf,?_⟩
  intro n
  filter_upwards [ae_restrict_of_ae hBa,ae_restrict_mem (hK n)] with x hxB hxK
  rw [hfg n hxK]
  exact indicator_of_mem hxB _

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.measurable_local_ae_pasting
