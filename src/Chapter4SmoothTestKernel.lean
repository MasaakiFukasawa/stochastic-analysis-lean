import Chapter4SmoothOpenApproximation
import Chapter4MarkovBorelExtension

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 2400000

/-- The smooth open approximations converge after integration against any
finite measure. This is the dominated-convergence step used twice in the
Markov proof. -/
theorem smooth_open_integral_limit {dim : ℕ}
    (O : Set (Fin dim → ℝ)) (hO : IsOpen O)
    (f : ℕ → (Fin dim → ℝ) → ℝ)
    (hf : ∀ n,Continuous (f n)) (hb : ∀ n x,f n x∈Icc 0 1)
    (hl : ∀ x,Tendsto (fun n => f n x) atTop (𝓝 (O.indicator (fun _ => (1:ℝ)) x)))
    (μ : Measure (Fin dim → ℝ)) [IsFiniteMeasure μ] :
    Tendsto (fun n => ∫ x,f n x ∂μ) atTop (𝓝 ((μ O).toReal)) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1:ℝ))
    (fun n => (hf n).aestronglyMeasurable) (integrable_const 1)
    (fun n => ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hb n x).1];exact (hb n x).2)
    (ae_of_all _ hl)
  simpa only [integral_indicator hO.measurableSet,integral_const,Measure.real,
    Measure.restrict_apply_univ,smul_eq_mul,mul_one] using hh

/-- Measurability of transition measures follows from their smooth compact
tests; it is not a separate kernel assumption. -/
theorem transition_measure_measurable_of_smooth_tests
    {A : Type*} [MeasurableSpace A] {dim : ℕ}
    (μ : A → Measure (Fin dim → ℝ)) [∀ a,IsProbabilityMeasure (μ a)]
    (hm : ∀ f : (Fin dim → ℝ) → ℝ,ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      Measurable (fun a => ∫ x,f x ∂μ a)) : Measurable μ := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    BorelSpace.measurable_eq isPiSystem_isOpen
  intro O hO
  obtain ⟨f,hf,hfc,hb,_,hl⟩ := smooth_monotone_open_approximation O hO
  have hreal : Measurable (fun a => (μ a O).toReal) :=
    measurable_of_tendsto_metrizable (fun n => hm (f n) (hf n) (hfc n))
      (tendsto_pi_nhds.mpr fun a => smooth_open_integral_limit O hO f (fun n => (hf n).continuous) hb hl (μ a))
  have he (a : A) : ENNReal.ofReal ((μ a O).toReal)=μ a O := ENNReal.ofReal_toReal (measure_ne_top _ _)
  simpa only [he] using hreal.ennreal_ofReal

end Asakura.Chapter4
