import Chapter4EulerEstimates
import Chapter2SignedDensityIntegral

open MeasureTheory Set
open scoped Topology
namespace Asakura.Chapter4

lemma interval_indicator_constant_integral (a b r c : ℝ) (ha : 0≤a) (hab : a≤b) (hr : 0≤r) :
    (∫ s in 0..r,(Ioc a b).indicator (fun _ => c) s)=c*(min b r-min a r) := by
  rw [intervalIntegral.integral_of_le hr,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have he : Ioc a b ∩ Ioc 0 r=Ioc a (min b r) := by
    ext x
    simp only [mem_inter_iff,mem_Ioc,le_min_iff]
    constructor
    · rintro ⟨⟨hxa,hxb⟩,⟨_,hxr⟩⟩;exact ⟨hxa,hxb,hxr⟩
    · rintro ⟨hxa,hxb,hxr⟩;exact ⟨⟨hxa,hxb⟩,⟨ha.trans_lt hxa,hxr⟩⟩
  rw [he,integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ]
  by_cases har : a≤r
  · rw [min_eq_left har,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr (le_min hab har))]
    ring
  · have hra : r≤a := le_of_not_ge har
    rw [min_eq_right (hra.trans hab),Ioc_eq_empty (not_lt_of_ge hra),measure_empty,ENNReal.toReal_zero,min_eq_right hra]
    ring

end Asakura.Chapter4
