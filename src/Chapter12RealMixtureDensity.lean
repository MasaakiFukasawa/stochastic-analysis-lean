import Chapter12ConvolutionDensity

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- A bounded continuous probability kernel produces the actual
continuous nonnegative convolution density. -/
theorem real_mixture_density {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [SFinite ν]
    [Measure.IsAddLeftInvariant ν]
    (g : E → ℝ) (hg : Continuous g) (hpos : ∀ x,0≤g x)
    (C : ℝ) (hbound : ∀ x,g x≤C) :
    (μ.prod (ν.withDensity (fun x => ENNReal.ofReal (g x)))).map (fun z : E × E => z.1+z.2)=
      ν.withDensity (fun z => ENNReal.ofReal (∫ x,g (z-x) ∂μ)) ∧
    Continuous (fun z => ∫ x,g (z-x) ∂μ) ∧
    (∀ z,0≤∫ x,g (z-x) ∂μ) ∧ (∀ z,(∫ x,g (z-x) ∂μ)≤C) := by
  have hb (z x : E) : ‖g (z-x)‖≤C := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hpos _)]
    exact hbound _
  have hi (z : E) : Integrable (fun x => g (z-x)) μ :=
    (integrable_const (μ := μ) C).mono' (by fun_prop) (ae_of_all _ (hb z))
  constructor
  · rw [convolution_mixture_density μ ν _ hg.measurable.ennreal_ofReal]
    congr 1
    funext z
    exact (ofReal_integral_eq_lintegral_ofReal (hi z) (ae_of_all _ (fun x => hpos (z-x)))).symm
  constructor
  · apply continuous_of_dominated
      (fun z => (show Continuous (fun x => g (z-x)) by fun_prop).aestronglyMeasurable)
      (fun z => ae_of_all μ (hb z))
      (integrable_const (μ := μ) C)
    exact ae_of_all _ (fun x => by fun_prop)
  constructor
  · intro z
    exact integral_nonneg (fun x => hpos _)
  · intro z
    calc
      (∫ x,g (z-x) ∂μ)≤∫ _ : E,C ∂μ :=
        integral_mono (hi z) (integrable_const _) (fun x => hbound _)
      _=C := by simp

end Asakura.Chapter12
