import Chapter5WeightedMembership
import Chapter5TimePrimitiveL2

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Exponential weighting changes the norm, not the almost-everywhere
equivalence relation used for the progressive Hilbert space. -/
theorem exponential_energy_ae_iff
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure (Ω × ℝ)) (β : ℝ) (p : Ω × ℝ → Prop) :
    (∀ᵐ z ∂exponentialEnergyMeasure ν β,p z) ↔ ∀ᵐ z ∂ν,p z := by
  unfold exponentialEnergyMeasure
  have hm : Measurable (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (β*z.2))) :=
    (measurable_const.mul measurable_snd).exp.ennreal_ofReal
  rw [ae_withDensity_iff hm]
  simp only [ne_eq,ENNReal.ofReal_eq_zero,not_le,Real.exp_pos,true_implies]

/-- Equality in the sample-time space implies equality of every primitive
on one common probability-one event, including the terminal primitive. -/
theorem time_primitive_common_congr
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (H G : Ω × ℝ → ℝ)
    (he : H =ᵐ[P.prod (volume.restrict (Ioc 0 R))] G) :
    ∀ᵐ w ∂P,∀ t ∈ Icc 0 R,(∫ r in 0..t,H (w,r)) = ∫ r in 0..t,G (w,r) := by
  filter_upwards [Measure.ae_ae_of_ae_prod he] with w hw
  intro t ht
  rw [intervalIntegral.integral_of_le ht.1,intervalIntegral.integral_of_le ht.1]
  exact integral_congr_ae (ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right ht.2) le_rfl) hw)

/-- The conditional-expectation construction of Y is independent of the
representative of the frozen driver, as an actual sample-time class. -/
theorem frozen_Y_quotient_independent
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0 ≤ R) (F : ℝ → MeasurableSpace Ω)
    (ξ : Ω → ℝ) (H G M N : Ω × ℝ → ℝ)
    (hH : Measurable H) (hG : Measurable G) (hM : Measurable M) (hN : Measurable N)
    (he : H =ᵐ[P.prod (volume.restrict (Ioc 0 R))] G)
    (hMC : ∀ t ∈ Icc 0 R,(fun w => M (w,t)) =ᵐ[P] P[(fun w => ξ w+(∫ r in 0..R,H (w,r)))|F t])
    (hNC : ∀ t ∈ Icc 0 R,(fun w => N (w,t)) =ᵐ[P] P[(fun w => ξ w+(∫ r in 0..R,G (w,r)))|F t]) :
    (fun z : Ω × ℝ => M z-(∫ r in 0..z.2,H (z.1,r))) =ᵐ[P.prod (volume.restrict (Ioc 0 R))]
      (fun z : Ω × ℝ => N z-(∫ r in 0..z.2,G (z.1,r))) := by
  have hp := time_primitive_common_congr P R H G he
  have hU : (fun w => ξ w+(∫ r in 0..R,H (w,r))) =ᵐ[P] (fun w => ξ w+(∫ r in 0..R,G (w,r))) := by
    filter_upwards [hp] with w hw
    rw [hw R ⟨hR,le_rfl⟩]
  have htime t (ht : t ∈ Icc 0 R) :
      (fun w => M (w,t)-(∫ r in 0..t,H (w,r))) =ᵐ[P] (fun w => N (w,t)-(∫ r in 0..t,G (w,r))) := by
    have hMN := (hMC t ht).trans ((condExp_congr_ae hU).trans (hNC t ht).symm)
    filter_upwards [hMN,hp] with w hw hpw
    rw [hw,hpw t ht]
  have hmeq := measurableSet_eq_fun (hM.sub (time_primitive_joint_measurable H hH))
    (hN.sub (time_primitive_joint_measurable G hG))
  apply (Measure.ae_prod_iff_ae_ae hmeq).mpr
  apply (Measure.ae_ae_comm hmeq).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact htime t ⟨ht.1.le,ht.2⟩

end Asakura.Chapter5
