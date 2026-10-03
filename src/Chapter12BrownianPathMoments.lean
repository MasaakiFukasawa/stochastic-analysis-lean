import Chapter12BrownianMaximumMoments

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem brownian_path_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) : MemLp X p P := by
  have hi := brownian_path_exponential_memLp P B hB hm hc T X hXm he 1 p hp
  apply hi.of_le hXm.aestronglyMeasurable
  apply ae_of_all
  intro w
  simp only [one_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  linarith [Real.add_one_le_exp ‖X w‖]

end Asakura.Chapter12
