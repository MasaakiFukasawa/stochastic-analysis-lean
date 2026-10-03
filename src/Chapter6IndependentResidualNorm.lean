import Chapter6GaussianVectorNorm
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The conditional triangle bound for a Gaussian bridge follows from
the independent residual and its ordinary expected norm. -/
theorem independent_residual_conditional_norm {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (R V : Ω → EuclideanSpace ℝ (Fin d)) (hRm : Measurable R) (hVm : Measurable V)
    (hR : MemLp R 2 P) (hV : MemLp V 2 P) (hind : IndepFun R V P)
    (a K : ℝ) (ha : 0≤a) (hb : (∫ w,‖R w‖ ∂P)≤K) :
    ∀ᵐ w ∂P,P[(fun w => ‖a • V w-R w‖)|MeasurableSpace.comap V inferInstance] w≤a*‖V w‖+K := by
  let G := MeasurableSpace.comap V inferInstance
  have hG : G≤m := hVm.comap_le
  have hiR := hR.norm.integrable (by norm_num)
  have hiV := hV.norm.integrable (by norm_num)
  have hiX : Integrable (fun w => ‖a • V w-R w‖) P := ((hV.const_smul a).sub hR).norm.integrable (by norm_num)
  have hiB : Integrable (fun w => a*‖V w‖+‖R w‖) P := (hiV.const_mul a).add hiR
  have hcond := condExp_mono hiX hiB (ae_of_all _ (fun w => by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha] using norm_sub_le (a • V w) (R w))) (m := G)
  letI : MeasurableSpace Ω := m
  have hRN : IndepFun (fun w => ‖R w‖) V P := hind.comp continuous_norm.measurable measurable_id
  have hzero := condExp_indep_eq hRm.norm.comap_le hG
    (show StronglyMeasurable[MeasurableSpace.comap (fun w => ‖R w‖) inferInstance] (fun w => ‖R w‖) from
      (Measurable.of_comap_le le_rfl).stronglyMeasurable) hRN
  have hVG : Measurable[G] V := Measurable.of_comap_le le_rfl
  have hVmeas : Measurable[G] (fun w => a*‖V w‖) := by
    letI : MeasurableSpace Ω := G
    exact hVG.norm.const_mul a
  have hfix := condExp_of_stronglyMeasurable hG hVmeas.stronglyMeasurable (hiV.const_mul a)
  have hadd := condExp_add (hiV.const_mul a) hiR G
  filter_upwards [hcond,hzero,hadd] with w hw hz hh
  change P[(fun w => a*‖V w‖+‖R w‖)|G] w=P[(fun w => a*‖V w‖)|G] w+P[(fun w => ‖R w‖)|G] w at hh
  rw [hh,hfix,hz] at hw
  exact hw.trans (add_le_add_right hb _)

end Asakura.Chapter6
