import ManuscriptLpComplete
import ManuscriptLpInequalities
import L2Moments
open MeasureTheory
namespace Asakura

/-- app1:193--199: the real polarization identity, expanded by bilinearity. -/
theorem manuscript_real_polarization {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f g : H) :
    inner ℝ f g = (‖f+g‖^2-‖f-g‖^2)/4 := by
  have ha := real_inner_add_add_self f g
  have hs := real_inner_sub_sub_self f g
  simp only [real_inner_self_eq_norm_sq] at ha hs
  linarith

/-- Any symmetric bilinear form inducing the given norm is the same inner product. -/
theorem manuscript_inner_unique {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (hsym : ∀ f g, B f g = B g f) (hdiag : ∀ f, B f f = ‖f‖^2) (f g : H) :
    B f g = inner ℝ f g := by
  have ha := hdiag (f+g)
  have hs := hdiag (f-g)
  simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply] at ha hs
  rw [hsym g f] at ha hs
  rw [manuscript_real_polarization]
  linarith

/-- The integral formula and the original uniqueness calculation agree in L2. -/
theorem manuscript_L2_polarization {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (μ : Measure Ω)
    (f g : Lp H 2 μ) :
    (∫ x, inner ℝ (f x) (g x) ∂μ) = (‖f+g‖^2-‖f-g‖^2)/4 := by
  rw [← L2.inner_def]
  exact manuscript_real_polarization f g

end Asakura
