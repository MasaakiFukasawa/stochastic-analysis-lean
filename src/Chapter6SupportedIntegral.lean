import Chapter5ClippedDriftIntegral

open MeasureTheory Set
namespace Asakura.Chapter6
open Asakura.Chapter5

lemma supported_integral_min (g : ℝ → ℝ) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hs : ∀ s,R < s → g s = 0) :
    (∫ s in 0..min R r,g s) = ∫ s in 0..r,g s := by
  have he : (Iic R).indicator g = g := by
    funext s
    by_cases h : s ≤ R
    · simp [h]
    · simp [h,hs s (lt_of_not_ge h)]
  have hh := clipped_driver_integral g R r hR hr
  rw [he,min_comm] at hh
  exact hh.symm

end Asakura.Chapter6
