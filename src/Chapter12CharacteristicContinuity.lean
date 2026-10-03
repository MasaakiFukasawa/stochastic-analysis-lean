import Chapter12GaussianMixtureFourier

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem characteristic_integral_continuous {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] :
    Continuous (fun ξ : E => ∫ y,Complex.exp (Complex.I*(inner ℝ ξ y:ℂ)) ∂μ) := by
  apply continuous_of_dominated (bound := fun _ : E => (1:ℝ))
    (fun ξ => (show Continuous (fun y : E => Complex.exp (Complex.I*(inner ℝ ξ y:ℂ))) by fun_prop).aestronglyMeasurable)
    (fun ξ => ae_of_all μ (fun y => by simp [Complex.norm_exp])) (integrable_const _)
  exact ae_of_all _ (fun y => by fun_prop)

end Asakura.Chapter12
