import Chapter12ProgressiveTerminalTrim

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

noncomputable def lpMeasureEquality {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ ν : Measure α) (he : μ=ν) : Lp E 2 μ ≃ₗᵢ[ℝ] Lp E 2 ν := by
  subst ν
  exact LinearIsometryEquiv.refl ℝ _

theorem lpMeasureEquality_coe {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ ν : Measure α) (he : μ=ν) (U : Lp E 2 μ) :
    (lpMeasureEquality μ ν he U : α → E)=(U : α → E) := by
  subst ν
  rfl

end Asakura.Chapter12
