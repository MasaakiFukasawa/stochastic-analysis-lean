import Chapter12LpInclusion

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12

theorem probabilityLpInclusion_injective {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] (hpq : p≤q) :
    Function.Injective (probabilityLpInclusion (E:=E) P p q hpq) := by
  intro f g h
  apply Lp.ext
  have hf := probabilityLpInclusion_coe P p q hpq f
  have hg := probabilityLpInclusion_coe P p q hpq g
  rw [h] at hf
  exact hf.symm.trans hg

end Asakura.Chapter12
