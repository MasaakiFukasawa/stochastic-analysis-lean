import Chapter12CallValueLimit
import Chapter12GraphClosure

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Closing the graph passes a smooth chain rule to a call payoff. The
no-atom condition is used solely for convergence of the derivatives at K. -/
theorem call_chain_by_closed_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (F : Ω → ℝ) (hF : Measurable F) (hFi : MemLp F p P)
    (u : Ω → H) (hu : MemLp u p P) (K : ℝ) (hno : P {w | F w = K} = 0)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεt : Tendsto ε atTop (𝓝 0))
    (hchain : ∀ n (hi : MemLp (fun w => smoothCall (ε n) K (F w)) p P)
      (hdi : MemLp (fun w => smoothCallSlope (ε n) K (F w) • u w) p P),
      (hi.toLp _,hdi.toLp _) ∈ D.graph) :
    ∃ (hi : MemLp (fun w => max (F w-K) 0) p P)
      (hdi : MemLp (fun w => (if K < F w then (1:ℝ) else 0) • u w) p P),
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  have hi : MemLp (fun w => max (F w-K) 0) p P :=
    (hFi.sub (memLp_const K)).of_le (by fun_prop) (ae_of_all P fun w => by
      change |max (F w-K) 0| ≤ |F w-K|
      rw [abs_of_nonneg (le_max_right (F w-K) 0)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hdi : MemLp (fun w => (if K < F w then (1:ℝ) else 0) • u w) p P :=
    hu.of_le (by
      have hm : Measurable (fun w => if K < F w then (1:ℝ) else 0) := by
        apply Measurable.ite (measurableSet_lt measurable_const hF) measurable_const measurable_const
      exact hm.aestronglyMeasurable.smul hu.aestronglyMeasurable)
      (ae_of_all P fun w => by split_ifs <;> simp)
  have hin n : MemLp (fun w => smoothCall (ε n) K (F w)) p P := by
    have he : MemLp (fun w => smoothCall (ε n) K (F w)-max (F w-K) 0) p P := by
      apply MemLp.of_bound (by unfold smoothCall; fun_prop) (ε n/2)
      exact ae_of_all P fun w => by
        have hb := smoothCall_error (ε n) K (F w) (hε n).le
        rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
        exact hb.2
    convert he.add hi using 1
    funext w
    exact (sub_add_cancel _ _).symm
  have hdin n : MemLp (fun w => smoothCallSlope (ε n) K (F w) • u w) p P := by
    have hm : Measurable (fun w => smoothCallSlope (ε n) K (F w)) := by
      unfold smoothCallSlope
      fun_prop
    apply hu.of_le (hm.aestronglyMeasurable.smul hu.aestronglyMeasurable)
    exact ae_of_all P fun w => by
      have hb := smoothCall_slope_bounds (ε n) K (F w) (hε n)
      change ‖smoothCallSlope (ε n) K (F w) • u w‖ ≤ ‖u w‖
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hb.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hb.2
  have hv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hin _ hi).mpr
    (call_value_Lp_limit P p F hF K ε (fun n => (hε n).le) hεt)
  have hd := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hdin _ hdi).mpr
    (call_derivative_Lp_limit P p (Fact.out : 1 ≤ p) hp F hF K hno u hu ε hε hεt)
  refine ⟨hi,hdi,?_⟩
  exact hD.mem_of_tendsto (hv.prodMk_nhds hd) (Eventually.of_forall fun n => hchain n (hin n) (hdin n))

end Asakura.Chapter12
