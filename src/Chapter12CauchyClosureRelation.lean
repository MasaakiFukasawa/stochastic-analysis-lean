import Chapter12DerivativeCauchyCriterion
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000

theorem cauchy_of_vanishing_distance {E:Type*} [NormedAddCommGroup E]
    (u v:ℕ → E) (hv:CauchySeq v) (r:ℕ → ℝ) (hr:Tendsto r atTop (𝓝 0))
    (h:∀n,dist (u n) (v n)≤r n) : CauchySeq u := by
  apply derivative_cauchy_criterion u v hv r hr 1 zero_le_one
  intro n m
  simp only [one_mul]
  have h1 := dist_triangle (u n) (v n) (u m)
  have h2 := dist_triangle (v n) (v m) (u m)
  have hn := h n
  have hm := h m
  rw [dist_comm (u m) (v m)] at hm
  simp only [dist_eq_norm] at h1 h2 hn hm
  linarith

theorem cauchy_closure_relation {A E F:Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f:A → E) (g:A → F)
    (hcore:∀c:ℕ → A,CauchySeq (fun n => f (c n)) → CauchySeq (fun n => g (c n)))
    (x:ℕ → E) (y:ℕ → F) (hx:CauchySeq x)
    (hxy:∀n,(x n,y n)∈closure (range (fun a => (f a,g a)))) : CauchySeq y := by
  let r := fun n:ℕ => (1:ℝ)/(n+1)
  have hr:Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex:∀n,∃a:A,dist (x n,y n) (f a,g a)<r n := by
    intro n
    obtain ⟨z,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp (hxy n) (r n) (by dsimp [r];positivity)
    exact ⟨a,ha⟩
  choose c hc using hex
  have hcx:∀n,dist (f (c n)) (x n)≤r n := by
    intro n
    have hh := hc n
    change max (dist (x n) (f (c n))) (dist (y n) (g (c n)))<r n at hh
    exact (dist_comm _ _).le.trans ((le_max_left _ _).trans hh.le)
  have hcy:∀n,dist (y n) (g (c n))≤r n := by
    intro n
    have hh := hc n
    change max (dist (x n) (f (c n))) (dist (y n) (g (c n)))<r n at hh
    exact (le_max_right _ _).trans hh.le
  have hf := cauchy_of_vanishing_distance _ x hx r hr hcx
  exact cauchy_of_vanishing_distance y _ (hcore c hf) r hr hcy
end Asakura.Chapter12
#print axioms Asakura.Chapter12.cauchy_closure_relation
