import Chapter4SmoothTestKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 2400000

/-- Smooth compact tests determine finite measures, by the manuscript's
open-set approximation and pi-lambda argument. -/
theorem measure_eq_of_smooth_compact_tests {dim : ℕ}
    (μ ν : Measure (Fin dim → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (he : ∀ f : (Fin dim → ℝ) → ℝ,ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      (∫ x,f x ∂μ)=∫ x,f x ∂ν) : μ=ν := by
  have ho O (hO : IsOpen O) : μ O=ν O := by
    obtain ⟨f,hf,hfc,hb,_,hl⟩ := smooth_monotone_open_approximation O hO
    have hμ := smooth_open_integral_limit O hO f (fun n => (hf n).continuous) hb hl μ
    have hν := smooth_open_integral_limit O hO f (fun n => (hf n).continuous) hb hl ν
    have hn : (fun n => ∫ x,f n x ∂μ)=(fun n => ∫ x,f n x ∂ν) := funext fun n => he (f n) (hf n) (hfc n)
    rw [hn] at hμ
    have hh := congrArg ENNReal.ofReal (tendsto_nhds_unique hμ hν)
    simpa only [ENNReal.ofReal_toReal (measure_ne_top μ O),
      ENNReal.ofReal_toReal (measure_ne_top ν O)] using hh
  exact ext_of_generate_finite {O | IsOpen O} BorelSpace.measurable_eq isPiSystem_isOpen
    (fun O hO => ho O hO) (ho univ isOpen_univ)

end Asakura.Chapter4
