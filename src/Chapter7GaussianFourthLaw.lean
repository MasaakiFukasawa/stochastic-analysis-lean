import Chapter7GaussianFourthMoment

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Asakura.Chapter7

theorem gaussian_fourth_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (v : ℝ≥0)
    (h : HasLaw X (gaussianReal 0 v) P) :
    Integrable (fun w => X w^4) P ∧ (∫ w,X w^4 ∂P)=3*(v:ℝ)^2 := by
  have hi : Integrable (fun x : ℝ => x^4) (gaussianReal 0 v) := by
    exact integrable_pow_of_mem_interior_integrableExpSet (by simp) 4
  constructor
  · exact h.integrable_comp hi
  · exact (h.integral_comp (f := fun x : ℝ => x^4) (by fun_prop)).trans (gaussian_fourth_moment v)

/-- Polarization of the fourth power, used to recover mixed fourth moments
without assuming independence of the four coordinates. -/
lemma fourth_polarization (x y z w : ℝ) :
    192*(x*y*z*w) =
      (x+y+z+w)^4-(x+y+z-w)^4-(x+y-z+w)^4+(x+y-z-w)^4-
      (x-y+z+w)^4+(x-y+z-w)^4+(x-y-z+w)^4-(x-y-z-w)^4 := by ring

end Asakura.Chapter7
