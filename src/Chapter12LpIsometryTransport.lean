import Chapter12LpMeasureEqualityToLp

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem lp_isometry_transport {α E G : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ ν : Measure α) (he : μ=ν) (I : Lp E 2 ν →ₗᵢ[ℝ] G) :
    ∃ J : Lp E 2 μ →ₗᵢ[ℝ] G,
      ∀ (f : α → E) (hμ : MemLp f 2 μ) (hν : MemLp f 2 ν),
        J (hμ.toLp f)=I (hν.toLp f) := by
  refine ⟨I.comp (lpMeasureEquality μ ν he).toLinearIsometry,?_⟩
  intro f hμ hν
  change I (lpMeasureEquality μ ν he (hμ.toLp f))=I (hν.toLp f)
  rw [lpMeasureEquality_toLp]

end Asakura.Chapter12
