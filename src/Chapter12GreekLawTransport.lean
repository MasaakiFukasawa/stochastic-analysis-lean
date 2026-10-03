import Chapter12GaussianTranslationDerivative

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem greek_derivative_transport {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (μ : Measure E) (Z : Ω → E) (hZ : HasLaw Z μ P)
    (f : ℝ → E → ℝ) (hm : ∀ s,Measurable (f s))
    (g : E → ℝ) (hg : Measurable g) (s : ℝ)
    (hd : HasDerivAt (fun u => ∫ z,f u z ∂μ) (∫ z,g z ∂μ) s) :
    HasDerivAt (fun u => ∫ w,f u (Z w) ∂P) (∫ w,g (Z w) ∂P) s := by
  have he (u : ℝ) : (∫ w,f u (Z w) ∂P)=∫ z,f u z ∂μ :=
    hZ.integral_comp (hm u).aestronglyMeasurable
  have hg' : (∫ w,g (Z w) ∂P)=∫ z,g z ∂μ := hZ.integral_comp hg.aestronglyMeasurable
  simp_rw [he,hg']
  exact hd

end Asakura.Chapter12
