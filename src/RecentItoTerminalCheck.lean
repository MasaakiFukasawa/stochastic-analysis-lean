import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith

/-! Endpoint construction: complete normed space, increment square bound,
Cauchy energy sequence. No terminal value of the process is assumed. -/
open Filter
open scoped Topology
namespace Asakura.RecentItoTerminal
variable {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]

theorem terminal_exists_of_energy_bound (X : ℕ → V) (a : ℕ → ℝ)
    (ha : CauchySeq a)
    (henergy : ∀ n m, ‖X n-X m‖ ^ 2 ≤ dist (a n) (a m)) :
    ∃ x : V, Tendsto X atTop (𝓝 x) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp ha (ε^2) (sq_pos_of_pos hε)
  refine ⟨N, ?_⟩
  intro n hn m hm
  have h := (henergy n m).trans_lt (hN n hn m hm)
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (X n-X m)]

theorem terminal_energy_identity (X : ℕ → V) (x : V) (a : ℕ → ℝ) (A : ℝ)
    (hX : Tendsto X atTop (𝓝 x)) (ha : Tendsto a atTop (𝓝 A))
    (hid : ∀ n, ‖X n‖ ^ 2 = a n) : ‖x‖ ^ 2 = A := by
  have hx := hX.norm.pow 2
  simp only [hid] at hx
  exact tendsto_nhds_unique hx ha

/-- The constructed limit and its energy are returned together. -/
theorem terminal_exists_with_isometry (X : ℕ → V) (a : ℕ → ℝ) (A : ℝ)
    (ha : Tendsto a atTop (𝓝 A))
    (henergy : ∀ n m, ‖X n-X m‖ ^ 2 ≤ dist (a n) (a m))
    (hid : ∀ n, ‖X n‖ ^ 2 = a n) :
    ∃ x : V, Tendsto X atTop (𝓝 x) ∧ ‖x‖ ^ 2 = A := by
  obtain ⟨x,hx⟩ := terminal_exists_of_energy_bound X a ha.cauchySeq henergy
  exact ⟨x,hx,terminal_energy_identity X x a A hx ha hid⟩
end Asakura.RecentItoTerminal
#print axioms Asakura.RecentItoTerminal.terminal_exists_of_energy_bound
#print axioms Asakura.RecentItoTerminal.terminal_energy_identity
#print axioms Asakura.RecentItoTerminal.terminal_exists_with_isometry
