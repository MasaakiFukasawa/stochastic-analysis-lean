import Chapter6IndependentResidualNorm

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem independent_residual_conditional_square {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (R V : Ω → EuclideanSpace ℝ (Fin d)) (hRm : Measurable R) (hVm : Measurable V)
    (hR : MemLp R 2 P) (hV : MemLp V 2 P) (hind : IndepFun R V P) (a : ℝ) :
    ∀ᵐ w ∂P,P[(fun w => ‖a • V w-R w‖^2)|MeasurableSpace.comap V inferInstance] w
      ≤2*a^2*‖V w‖^2+2*(∫ w,‖R w‖^2 ∂P) := by
  let G := MeasurableSpace.comap V inferInstance
  letI : MeasurableSpace Ω := m
  have hG : G≤m := hVm.comap_le
  have hiR := hR.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hiV := hV.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hiX : Integrable (fun w => ‖a • V w-R w‖^2) P :=
    ((hV.const_smul a).sub hR).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hiB : Integrable (fun w => 2*a^2*‖V w‖^2+2*‖R w‖^2) P :=
    (hiV.const_mul (2*a^2)).add (hiR.const_mul 2)
  have hb w : ‖a • V w-R w‖^2≤2*a^2*‖V w‖^2+2*‖R w‖^2 := by
    have hh := norm_sub_le (a • V w) (R w)
    rw [norm_smul,Real.norm_eq_abs] at hh
    have hsq := sq_abs a
    nlinarith [norm_nonneg (a • V w-R w),norm_nonneg (V w),norm_nonneg (R w),abs_nonneg a,
      sq_nonneg (|a| * ‖V w‖-‖R w‖)]
  have hcond := condExp_mono (m := G) hiX hiB (ae_of_all _ hb)
  have hind' : IndepFun (fun w => ‖R w‖^2) V P := hind.comp (continuous_norm.pow 2).measurable measurable_id
  have hzero := condExp_indep_eq (hRm.norm.pow_const 2).comap_le hG
    (show StronglyMeasurable[MeasurableSpace.comap (fun w => ‖R w‖^2) inferInstance] (fun w => ‖R w‖^2) from
      (Measurable.of_comap_le le_rfl).stronglyMeasurable) hind'
  have hVG : Measurable[G] V := Measurable.of_comap_le le_rfl
  have hVmeas : Measurable[G] (fun w => 2*a^2*‖V w‖^2) := by
    letI : MeasurableSpace Ω := G
    exact (hVG.norm.pow_const 2).const_mul _
  have hfix := condExp_of_stronglyMeasurable hG hVmeas.stronglyMeasurable (hiV.const_mul (2*a^2))
  have hadd := condExp_add (hiV.const_mul (2*a^2)) (hiR.const_mul 2) G
  have hsm := condExp_smul (μ := P) (2:ℝ) (fun w => ‖R w‖^2) G
  filter_upwards [hcond,hzero,hadd,hsm] with w hw hz hh hs
  change P[(fun w => 2*a^2*‖V w‖^2+2*‖R w‖^2)|G] w=P[(fun w => 2*a^2*‖V w‖^2)|G] w+P[(fun w => 2*‖R w‖^2)|G] w at hh
  change P[(fun w => 2*‖R w‖^2)|G] w=2*P[(fun w => ‖R w‖^2)|G] w at hs
  rwa [hh,hfix,hs,hz] at hw

end Asakura.Chapter6
