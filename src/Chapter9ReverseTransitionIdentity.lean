import Chapter9ReverseIntegratedGenerator
import Chapter9ReverseTransitionFields

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The analytic generator formula in exactly the time parametrization of
 the reversed process, with an ordinary finite-measure integral. -/
theorem ou_reverse_transition_identity {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (T s t : ℝ) (hst : s<t) (htT : t<T) (x : Fin d → ℝ) :
    ouReverseParamTransition μ T s (fun z => f z.2) (t,x) = f x+
      ∫ h,ouReverseParamTransition μ T s
        (fun z => ouReverseGenerator μ f (T-z.1,z.2)) (s+h,x)
        ∂volume.restrict (Ioc 0 (t-s)) := by
  obtain ⟨hi,he⟩ := reverse_ou_integrated_generator μ f hf hfc (T-s) (t-s)
    (sub_pos.mpr hst) (by linarith) x
  have hd : (T-s)-(t-s)=T-t := by ring
  have hh (h : ℝ) (hh : h∈Ioc 0 (t-s)) :
      (∫ y,ouCoordinateDensity μ (T-s-h,y)*
        reverseTest (fun y => ouCoordinateDensity μ (T-s-h,y)) f y*
        gaussianKernel (Real.exp (-h)) (1-Real.exp (-2*h)) y x)/
          ouCoordinateDensity μ (T-s,x) =
      ouReverseParamTransition μ T s
        (fun z => ouReverseGenerator μ f (T-z.1,z.2)) (s+h,x) := by
    unfold ouReverseParamTransition
    have ha : s+h-s=h := by ring
    have hb : T-(s+h)=T-s-h := by ring
    dsimp only
    rw [ha,hb]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    rw [ou_reverse_generator_eq μ f _ (by linarith [hh.2]) y]
    ring
  rw [intervalIntegral.integral_of_le (sub_nonneg.mpr hst.le)] at he
  have heq := integral_congr_ae (Filter.Eventually.mono (ae_restrict_mem (μ := volume) measurableSet_Ioc) hh)
  change (∫ y,f y*ouCoordinateDensity μ (T-s-(t-s),y)*
    gaussianKernel (Real.exp (-(t-s))) (1-Real.exp (-2*(t-s))) y x)/
    ouCoordinateDensity μ (T-s,x)-f x = _ at he
  rw [hd] at he
  change ouReverseParamTransition μ T s (fun z => f z.2) (t,x)-f x = _ at he
  have heq' := he.trans (by simpa only [ouCoordinateDensity] using! heq)
  linarith
end Asakura.Chapter9
