import Chapter7BrownianCellIntegrand

open MeasureTheory Set
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000

/-- Restrict a cell to the elapsed observation interval and shift its origin. -/
lemma cell_integral_restriction (f : ℝ → ℝ) (s h t : ℝ) (hs : 0≤s) (hh : 0≤h) (ht : 0≤t) :
    (∫ r in 0..t,(Ioc s (s+h)).indicator f r)=
      ∫ r in 0..max 0 (min h (t-s)),f (s+r) := by
  rw [intervalIntegral.integral_of_le ht,integral_indicator measurableSet_Ioc]
  rw [Measure.restrict_restrict measurableSet_Ioc]
  have hi : Ioc s (s+h) ∩ Ioc 0 t=Ioc s (min (s+h) t) := by
    ext r
    simp only [mem_inter_iff,mem_Ioc,le_min_iff]
    constructor
    · rintro ⟨⟨hr,hre⟩,⟨_,hrt⟩⟩
      exact ⟨hr,hre,hrt⟩
    · rintro ⟨hr,hre,hrt⟩
      exact ⟨⟨hr,hre⟩,⟨lt_of_le_of_lt hs hr,hrt⟩⟩
  rw [hi]
  by_cases hst : t≤s
  · have hempty : Ioc s (min (s+h) t)=∅ := Ioc_eq_empty_of_le ((min_le_right _ _).trans hst)
    have hz : max 0 (min h (t-s))=0 := max_eq_left ((min_le_right _ _).trans (sub_nonpos.mpr hst))
    simp only [hempty,hz,Measure.restrict_empty,integral_zero_measure,intervalIntegral.integral_same]
  · have hst' : s≤t := (lt_of_not_ge hst).le
    have hbound : s≤min (s+h) t := le_min (le_add_of_nonneg_right hh) hst'
    rw [← intervalIntegral.integral_of_le hbound]
    have hz : max 0 (min h (t-s))=min h (t-s) := max_eq_right (le_min hh (sub_nonneg.mpr hst'))
    rw [hz,intervalIntegral.integral_comp_add_left]
    have he : s+min h (t-s)=min (s+h) t := by rw [add_min,add_sub_cancel]
    rw [add_zero,he]

end Asakura.Chapter7
