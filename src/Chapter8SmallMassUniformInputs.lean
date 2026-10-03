import Chapter8BrownianLinearMoment
import Chapter8DampedGivenNoiseMoment
import Chapter8SmallMassErrorMoment

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The initial and noise terms in the position Volterra formula have
uniform moment bounds. No rank condition on the noise matrix is used. -/
theorem small_mass_uniform_inputs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (Γ M : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (S : Fin d → Fin n → ℝ) (α m t T : ℝ) (hα : 0<α) (hm : 0<m) (hm1 : m≤1)
    (ht : 0≤t) (htT : t≤T)
    (hΓ : ∀ x,α*‖x‖^2≤⟪x,Γ x⟫)
    (q v : Ω → EuclideanSpace ℝ (Fin d)) (hq : MemLp q 2 P) (hv : MemLp v 2 P)
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => (NormedSpace.exp ((t-z.2) • (-m⁻¹ • Γ)) (WithLp.toLp 2 (fun i => S i j))) i) (N i j)) :
    let A := fun w => q w+m • M (v w-NormedSpace.exp (t • (-m⁻¹ • Γ)) (v w))
    let Z := fun w => M (WithLp.toLp 2 (fun i => ∑ j,S i j*B.W j (realTimeClamp t) w)-
      WithLp.toLp 2 (fun i => ∑ j,N i j (realTimeClamp t) w))
    let CB := ∑ j,‖WithLp.toLp 2 (fun i => S i j)‖^2
    MemLp A 2 P ∧ MemLp Z 2 P ∧
      (∫ w,‖A w‖^2 ∂P)≤3*((∫ w,‖q w‖^2 ∂P)+4*‖M‖^2*(∫ w,‖v w‖^2 ∂P)) ∧
      (∫ w,‖Z w‖^2 ∂P)≤3*‖M‖^2*(T*CB+CB/(2*α)) := by
  let E0 := NormedSpace.exp (t • (-m⁻¹ • Γ))
  have hE : ‖E0‖≤1 := (damped_semigroup_norm_bound Γ α m hm hΓ t ht).trans
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) ht) hm.le))
  have hvel := initial_velocity_second_moment P M E0 hE m hm.le v hv
  have hW := brownian_linear_second_moment P B S t ht
  have hZ := damped_noise_given_second_moment P B Γ α m t hα hm ht hΓ
    (fun j => WithLp.toLp 2 (fun i => S i j)) N hN hNI
  let W := fun w => WithLp.toLp 2 (fun i => ∑ j,S i j*B.W j (realTimeClamp t) w)
  let Z := fun w => WithLp.toLp 2 (fun i => ∑ j,N i j (realTimeClamp t) w)
  let CB := ∑ j,‖WithLp.toLp 2 (fun i => S i j)‖^2
  have hCB : 0≤CB := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdiff : MemLp (fun w => W w-Z w) 2 P := hW.1.sub hZ.1
  have hMdiff := random_linear_second_moment P M (fun w => W w-Z w) hdiff
  dsimp only
  refine ⟨hq.add hvel.1,hMdiff.1,?_,?_⟩
  · have hs := random_three_sum_square P q (fun w => m • M (v w-E0 (v w))) (fun _ => 0) hq hvel.1 MemLp.zero
    simp only [add_zero,norm_zero,zero_pow (by decide : 2≠0),integral_zero] at hs
    have hm2 : m^2≤1 := by nlinarith
    have hmoment : 0≤∫ w,‖v w‖^2 ∂P := integral_nonneg (fun _ => sq_nonneg _)
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm2 (by norm_num : (0:ℝ)≤4)) (sq_nonneg ‖M‖)) hmoment
    have hh := hvel.2.trans hb
    nlinarith
  · have hs := random_three_sum_square P W (fun w => -Z w) (fun _ => 0) hW.1 hZ.1.neg MemLp.zero
    simp only [add_zero,norm_zero,zero_pow (by decide : 2≠0),integral_zero,norm_neg,←sub_eq_add_neg] at hs
    have hwb : (∫ w,‖W w‖^2 ∂P)≤T*CB := by rw [hW.2]; exact mul_le_mul_of_nonneg_right htT hCB
    have hzb : (∫ w,‖Z w‖^2 ∂P)≤CB/(2*α) := hZ.2.trans (by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_of_le_one_right hCB hm1)
    have hsum : (∫ w,‖W w-Z w‖^2 ∂P)≤3*(T*CB+CB/(2*α)) := by nlinarith
    have hh := hMdiff.2.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg ‖M‖))
    convert hh using 1 <;> ring
end Asakura.Chapter8
