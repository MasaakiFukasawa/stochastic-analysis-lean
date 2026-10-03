import Chapter2LocalLpPasting
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem convergence_in_measure_mono_measure
    {S : Type*} [MeasurableSpace S] {μ ν : Measure S} (hμ : μ ≤ ν)
    {f : ℕ → S → ℝ} {g : S → ℝ} (hf : TendstoInMeasure ν f atTop g) :
    TendstoInMeasure μ f atTop g := by
  intro ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hf ε hε)
    (fun _ => zero_le) (fun n => hμ _)

/-- Coordinatewise Lp-Cauchy sequences of local functions have a single
measurable local Lp limit. The covering sets need not increase, have finite
mass, or carry sigma-finite restrictions. Compatibility of the independently
constructed Lp limits is proved on every overlap. -/
theorem local_lp_cauchy_limit
    {S : Type*} [MeasurableSpace S] (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : ℕ → Set S) (hK : ∀ j, MeasurableSet (K j))
    (f : ℕ → S → ℝ) (hf : ∀ n j, MemLp (f n) p (μ.restrict (K j)))
    (hC : ∀ j, CauchySeq (fun n => (hf n j).toLp (f n))) :
    ∃ g : S → ℝ, Measurable g ∧ ∀ j, ∃ hg : MemLp g p (μ.restrict (K j)),
      Tendsto (fun n => (hf n j).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hex j : ∃ g : Lp ℝ p (μ.restrict (K j)),
      Tendsto (fun n => (hf n j).toLp (f n)) atTop (𝓝 g) := by
    letI : CompleteSpace (Lp ℝ p (μ.restrict (K j))) := current_lp_complete
    exact cauchySeq_tendsto_of_complete (hC j)
  choose u hu using hex
  let v := fun j => (Lp.aestronglyMeasurable (u j)).mk (u j)
  have hv j : Measurable (v j) := (Lp.aestronglyMeasurable (u j)).stronglyMeasurable_mk.measurable
  have huv j : (u j : S → ℝ) =ᵐ[μ.restrict (K j)] v j := (Lp.aestronglyMeasurable (u j)).ae_eq_mk
  have ht j : TendstoInMeasure (μ.restrict (K j)) f atTop (v j) := by
    apply (tendstoInMeasure_of_tendsto_Lp (hu j)).congr
    · intro n
      exact (hf n j).coeFn_toLp
    · exact huv j
  have hcompat i j : v i =ᵐ[μ.restrict (K i ∩ K j)] v j := by
    apply tendstoInMeasure_ae_unique
      (convergence_in_measure_mono_measure (Measure.restrict_mono inter_subset_left le_rfl) (ht i))
      (convergence_in_measure_mono_measure (Measure.restrict_mono inter_subset_right le_rfl) (ht j))
  obtain ⟨g,hg,hgv⟩ := measurable_local_ae_pasting μ K hK v hv hcompat
  refine ⟨g,hg,?_⟩
  intro j
  have heu : (u j : S → ℝ) =ᵐ[μ.restrict (K j)] g := (huv j).trans (hgv j).symm
  have hgi : MemLp g p (μ.restrict (K j)) := (Lp.memLp (u j)).ae_eq heu
  refine ⟨hgi,?_⟩
  have he : hgi.toLp g = u j := Lp.ext (hgi.coeFn_toLp.trans heu.symm)
  rw [he]
  exact hu j

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_lp_cauchy_limit
