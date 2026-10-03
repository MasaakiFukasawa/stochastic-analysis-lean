import FullAuditLangevinContraction
import Mathlib.Analysis.SpecificLimits.Normed

open Filter
open scoped Topology
namespace Asakura.Chapter8

/-- The pullback convergence argument in the Banach space L². The cocycle
identity and the uniform one-step moment bound give the summable increments;
convergence is obtained from completeness, not assumed. -/
theorem pullback_geometric_limit {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℕ → E → E) (ξ : ℕ → E) (ρ C : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hLip : ∀ n x y, ‖F n x-F n y‖ ≤ ρ^n*‖x-y‖)
    (hξ : ∀ n, ‖ξ n‖ ≤ C)
    (hflow : ∀ n, F (n+1) 0 = F n (ξ n)) :
    ∃ Y : E, Tendsto (fun n => F n 0) atTop (nhds Y) ∧
      ∀ n, ‖F n 0-Y‖ ≤ C*ρ^n/(1-ρ) := by
  have hincr (n : ℕ) : dist (F n 0) (F (n+1) 0) ≤ C*ρ^n := by
    rw [hflow,dist_comm,dist_eq_norm]
    have hh := (hLip n (ξ n) 0).trans (mul_le_mul_of_nonneg_left
      (by simpa using hξ n) (pow_nonneg hρ n))
    simpa only [mul_comm] using hh
  obtain ⟨Y,hY⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric ρ C hρ1 hincr)
  refine ⟨Y,hY,?_⟩
  intro n
  simpa only [dist_eq_norm] using dist_le_of_le_geometric_of_tendsto ρ C hρ1 hincr hY n

/-- Continuity of the forward evolution transports the pullback limit. -/
theorem forward_pullback_limit {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (Y : ℕ → E) (y : E) (G : E → F) (hY : Tendsto Y atTop (nhds y))
    (hG : ContinuousAt G y) : Tendsto (fun n => G (Y n)) atTop (nhds (G y)) :=
  hG.tendsto.comp hY

end Asakura.Chapter8
