import Chapter8WeightedOperatorMoment
import Chapter8DampedSemigroup
import Chapter8SmallMassBounds

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The O(m²) estimate for the actual drift remainder follows from its
uniform second moment and the square of the exponential kernel's mass. -/
theorem damped_drift_second_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Γ : E →L[ℝ] E)
    (α m T C : ℝ) (hα : 0<α) (hm : 0<m) (hT : 0≤T) (hC : 0≤C)
    (hΓ : ∀ x,α*‖x‖^2≤⟪x,Γ x⟫)
    (H : Ω × ℝ → E) (hH : Measurable H)
    (h2 : MemLp H 2 (P.prod (volume.restrict (Ioc 0 T))))
    (hb : ∀ s∈Icc 0 T,(∫ w,‖H (w,s)‖^2 ∂P)≤C) :
    MemLp (fun w => ∫ s in 0..T,NormedSpace.exp ((T-s) • (-m⁻¹ • Γ)) (H (w,s))) 2 P ∧
      (∫ w,‖∫ s in 0..T,NormedSpace.exp ((T-s) • (-m⁻¹ • Γ)) (H (w,s))‖^2 ∂P)≤C*m^2/α^2 := by
  let k : ℝ → ℝ≥0 := fun s => ⟨Real.exp (-α*(T-s)/m),(Real.exp_pos _).le⟩
  have hk : Continuous k := (show Continuous (fun s : ℝ => Real.exp (-α*(T-s)/m)) by fun_prop).subtype_mk _
  have hkp s : 0<k s := Real.exp_pos _
  have hk1 : ∀ᵐ s ∂volume.restrict (Ioc 0 T),k s≤1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    change Real.exp (-α*(T-s)/m)≤1
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) (sub_nonneg.mpr hs.2)) hm.le
  let K := fun s : ℝ => NormedSpace.exp ((T-s) • (-m⁻¹ • Γ))
  have hK : Continuous K := (continuous_iff_continuousAt.mpr (fun r =>
    (hasDerivAt_exp_smul_const (-m⁻¹ • Γ) r).continuousAt)).comp (continuous_const.sub continuous_id)
  have hKb : ∀ᵐ s ∂volume.restrict (Ioc 0 T),‖K s‖≤(k s:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact damped_semigroup_norm_bound Γ α m hm hΓ (T-s) (sub_nonneg.mpr hs.2)
  have hh := weighted_operator_moment P (volume.restrict (Ioc 0 T)) k hk.measurable hkp hk1 K hK hKb H hH h2 C
    ((ae_restrict_mem measurableSet_Ioc).mono (fun s hs => hb s ⟨hs.1.le,hs.2⟩))
  have he : (∫ s,(k s:ℝ) ∂volume.restrict (Ioc 0 T))=(∫ s in 0..T,Real.exp (-α*(T-s)/m)) := by
    rw [intervalIntegral.integral_of_le hT]
    rfl
  rw [he] at hh
  have hmass := small_mass_kernel_bound α m T hα hm hT
  have hs := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hmass.1 hmass.2 2) hC
  refine ⟨by simpa only [intervalIntegral.integral_of_le hT,K] using hh.1,?_⟩
  have hb := hh.2.trans hs
  convert hb using 1
  · simp only [intervalIntegral.integral_of_le hT,K]
  · ring
end Asakura.Chapter8
