import Chapter12LpMeasureEquality

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem lpMeasureEquality_toLp {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ ν : Measure α) (he : μ=ν) (f : α → E) (hμ : MemLp f 2 μ) (hν : MemLp f 2 ν) :
    lpMeasureEquality μ ν he (hμ.toLp f)=hν.toLp f := by
  subst ν
  rfl

end Asakura.Chapter12
