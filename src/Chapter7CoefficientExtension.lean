import Chapter7TimeChangeSDEWritten

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7

/-- A coefficient given only at nonnegative times has a continuous constant
extension below zero. Thus the real-time coefficient used by the clock-ODE
formalization imposes no additional regularity assumption. -/
theorem coefficient_nonnegative_time_extension
    (σ : ℝ → ℝ≥0 → ℝ) (hc : Continuous (fun z : ℝ × ℝ≥0 => σ z.1 z.2))
    (hn : ∀ x t,σ x t ≠ 0) :
    let σ' := fun x t => σ x (Real.toNNReal t)
    Continuous (fun z : ℝ × ℝ => σ' z.1 z.2) ∧
      (∀ x t,σ' x t ≠ 0) ∧ (∀ x (t : ℝ≥0),σ' x t = σ x t) := by
  refine ⟨hc.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd)),(fun x t => hn x (Real.toNNReal t)),?_⟩
  intro x t
  simp only [Real.toNNReal_coe]

end Asakura.Chapter7
