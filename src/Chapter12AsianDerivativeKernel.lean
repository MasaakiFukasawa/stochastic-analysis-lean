import Chapter12IntegralOfSobolevFamily
import Chapter12TimeDirectionContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
namespace Asakura.Chapter12
set_option maxHeartbeats 1200000

/-- The pointwise time kernel of the derivative of a time integral.
The exceptional endpoint s=0 is irrelevant to the time L2 class. -/
theorem integrated_prefix_kernel (T s : ℝ) (hs : 0 < s) (hsT : s ≤ T) (a : ℝ → ℝ) :
    (∫ t in Ioc (0:ℝ) T, a t * (Ioc (0:ℝ) t).indicator (fun _ => (1:ℝ)) s) =
      ∫ t in s..T,a t := by
  have he : (fun t => a t * (Ioc (0:ℝ) t).indicator (fun _ => (1:ℝ)) s) =
      (Ici s).indicator a := by
    funext t
    by_cases h : s ≤ t
    · simp [h,hs]
    · simp [h,hs]
  rw [he,integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  have hi : Ici s ∩ Ioc (0:ℝ) T = Icc s T := by
    ext t
    simp only [mem_inter_iff,mem_Ici,mem_Ioc,mem_Icc]
    constructor
    · intro h
      exact ⟨h.1,h.2.2⟩
    · intro h
      exact ⟨h.1,hs.trans_le h.1,h.2⟩
  rw [hi,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hsT]

end Asakura.Chapter12
