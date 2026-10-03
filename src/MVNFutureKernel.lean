import MVNKernelIntegrability
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set
namespace Asakura

lemma mvn_past_memLp (H t : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (ht : 0 ≤ t) :
    MemLp (mvnPastKernel (H-1/2) t) 2 (volume.restrict (Ioi 0)) := by
  apply (memLp_two_iff_integrable_sq (by unfold mvnPastKernel; fun_prop)).mpr
  exact mvn_past_square_integrable (H-1/2) t (by linarith) (by linarith) ht

lemma mvn_future_square_integrable (a t : ℝ) (ha : -1/2 < a) (ht : 0 ≤ t) :
    IntegrableOn (fun s => ((t-s)^a)^2) (Ioc 0 t) := by
  have hi : IntervalIntegrable (fun x : ℝ => x^(2*a)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hc : IntervalIntegrable (fun s : ℝ => (t-s)^(2*a)) volume 0 t := by
    simpa using (hi.comp_sub_left t).symm
  have hii := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hc
  apply hii.congr_fun _ measurableSet_Ioc
  intro s hs
  change (t-s)^(2*a) = ((t-s)^a)^2
  symm
  rw [← Real.rpow_natCast,← Real.rpow_mul (sub_nonneg.mpr hs.2)]
  congr 1; ring

lemma mvn_future_memLp (H t : ℝ) (hH : 0 < H) (ht : 0 ≤ t) :
    MemLp (fun s => (t-s)^(H-1/2)) 2 (volume.restrict (Ioc 0 t)) := by
  apply (memLp_two_iff_integrable_sq
    ((measurable_const.sub measurable_id |>.pow_const _).aestronglyMeasurable)).mpr
  exact mvn_future_square_integrable (H-1/2) t (by linarith) ht

lemma mvn_future_variance (H t : ℝ) (hH : 0 < H) (ht : 0 ≤ t) :
    (∫ s in Ioc 0 t, ((t-s)^(H-1/2))^2) = t^(2*H)/(2*H) := by
  have he : (∫ s in Ioc 0 t, ((t-s)^(H-1/2))^2) =
      ∫ s in Ioc 0 t, (t-s)^(2*H-1) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change ((t-s)^(H-1/2))^2 = (t-s)^(2*H-1)
    rw [← Real.rpow_natCast,← Real.rpow_mul (sub_nonneg.mpr hs.2)]
    congr 1; ring
  rw [he,← intervalIntegral.integral_of_le ht]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^(2*H-1)) t]
  simp only [sub_self,sub_zero]
  rw [integral_rpow (Or.inl (by linarith : -1 < 2*H-1))]
  have hp : 2*H-1+1 = 2*H := by ring
  rw [hp,Real.zero_rpow (by positivity : 2*H ≠ 0),sub_zero]
end Asakura
