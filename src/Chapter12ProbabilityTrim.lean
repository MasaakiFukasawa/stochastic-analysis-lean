import Chapter12TrimWiener

open MeasureTheory
namespace Asakura.Chapter12

theorem probability_trim {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (mT : MeasurableSpace Ω) (hle : mT ≤ m) :
    IsProbabilityMeasure (P.trim hle) := by
  constructor
  rw [trim_measurableSet_eq hle MeasurableSet.univ]
  exact measure_univ

end Asakura.Chapter12
