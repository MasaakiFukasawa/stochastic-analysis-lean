import Chapter12CallChainLimit

open MeasureTheory Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Uniform payoff approximation yields Lp convergence, including the
unbounded payoff itself. No boundedness assumption on F is inserted. -/
theorem call_value_Lp_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ≥0∞)
    (F : Ω → ℝ) (hF : Measurable F) (K : ℝ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hεt : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun w => smoothCall (ε n) K (F w)-max (F w-K) 0) p P)
      atTop (𝓝 0) := by
  have hb n : eLpNorm (fun w => smoothCall (ε n) K (F w)-max (F w-K) 0) p P
      ≤ ENNReal.ofReal (ε n/2) := by
    have hm : Measurable (fun w => smoothCall (ε n) K (F w)-max (F w-K) 0) := by
      unfold smoothCall
      fun_prop
    have h := eLpNorm_le_of_ae_bound (p := p) hm.aestronglyMeasurable
      (ae_of_all P fun w => by
        have he := smoothCall_error (ε n) K (F w) (hε n)
        rw [Real.norm_eq_abs,abs_of_nonneg he.1]
        exact he.2)
    simpa only [measure_univ,ENNReal.one_rpow,mul_one,one_mul] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
    (fun _ => bot_le) hb
  simpa only [zero_div,ENNReal.ofReal_zero,ENNReal.bot_eq_zero] using ENNReal.tendsto_ofReal (hεt.div_const 2)

end Asakura.Chapter12
