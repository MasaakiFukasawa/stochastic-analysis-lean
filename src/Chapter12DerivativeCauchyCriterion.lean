import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1200000

theorem derivative_cauchy_criterion {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (u : ℕ → E) (v : ℕ → F) (hv : CauchySeq v)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (C : ℝ) (hC : 0≤C)
    (hb : ∀n m,‖u n-u m‖≤C*(‖v n-v m‖+r n+r m)) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let d := ε/(3*(C+1))
  have hd : 0<d := div_pos hε (by positivity)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hv d hd
  have hr' : ∀ᶠn in atTop,r n<d := hr.eventually (gt_mem_nhds hd)
  obtain ⟨M,hM⟩ := eventually_atTop.mp hr'
  refine ⟨max N M,?_⟩
  intro n hn m hm
  have hnN := (le_max_left N M).trans hn
  have hmN := (le_max_left N M).trans hm
  have hnM := (le_max_right N M).trans hn
  have hmM := (le_max_right N M).trans hm
  have hvd := hN n hnN m hmN
  rw [dist_eq_norm] at hvd
  rw [dist_eq_norm]
  have hs : ‖v n-v m‖+r n+r m<3*d := by linarith [hM n hnM,hM m hmM]
  have heq : 3*(C+1)*d=ε := by
    dsimp only [d]
    exact mul_div_cancel₀ ε (ne_of_gt (by positivity : 0<3*(C+1)))
  have hh := mul_le_mul_of_nonneg_left hs.le hC
  have hu := hb n m
  nlinarith
end Asakura.Chapter12
#print axioms Asakura.Chapter12.derivative_cauchy_criterion
