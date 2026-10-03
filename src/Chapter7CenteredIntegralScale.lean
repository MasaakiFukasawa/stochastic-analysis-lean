import Chapter7MeanSquareProbability

open MeasureTheory
namespace Asakura.Chapter7

lemma centered_integral_scale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Ω → ℝ) (a : ℝ) :
    (∫ w,(a*U w-(∫ v,a*U v ∂P))^2 ∂P)=
      a^2*(∫ w,(U w-(∫ v,U v ∂P))^2 ∂P) := by
  rw [integral_const_mul]
  have he w : (a*U w-a*(∫ v,U v ∂P))^2=a^2*(U w-(∫ v,U v ∂P))^2 := by ring
  simp_rw [he]
  exact integral_const_mul _ _

end Asakura.Chapter7
