import Chapter8DeterministicVectorMoment
import Chapter8DampedSemigroup
import Chapter8SmallMassBounds
import Chapter6BoundedVectorConstruction

open MeasureTheory Set
open scoped BigOperators NNReal RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The noise remainder is constructed as actual Ito integrals and its
mean-square norm is O(m), uniformly over finite terminal times. -/
theorem damped_noise_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (Γ : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (α m T : ℝ) (hα : 0<α) (hm : 0<m) (hT : 0≤T)
    (hΓ : ∀ x,α*‖x‖^2≤⟪x,Γ x⟫) (b : Fin n → EuclideanSpace ℝ (Fin d)) :
    ∃ N : Fin d → Fin n → HalfClosedTime → Ω → ℝ,
      (∀ i j,LocalMProcessWitness P B.F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => (NormedSpace.exp ((T-z.2) • (-m⁻¹ • Γ)) (b j)) i) (N i j)) ∧
      (∫ w,‖WithLp.toLp 2 (fun i => ∑ j,N i j (realTimeClamp T) w)‖^2 ∂P)≤
        (∑ j,‖b j‖^2)*m/(2*α) := by
  let A := -m⁻¹ • Γ
  let E := fun r : ℝ => NormedSpace.exp (r • A)
  have hEc : Continuous E := continuous_iff_continuousAt.mpr (fun r => (hasDerivAt_exp_smul_const A r).continuousAt)
  let G := fun i j r => (E (T-r) (b j)) i
  have hG i j : Continuous (G i j) := (EuclideanSpace.proj i).continuous.comp
    ((hEc.comp (continuous_const.sub continuous_id)).clm_apply continuous_const)
  have hex i j := continuous_adapted_ito_exists P (show (0:EReal)<⊤ by simp) B.F B.mono B.le B.null
    (B.W j) (B.martingale j) (fun z => G i j z.2) (fun r _ _ => by
      change Measurable[B.F (realTimeClamp r)] (fun _ : Ω => G i j r)
      exact measurable_const)
    (fun _ _ _ _ => (hG i j).continuousOn)
  choose N hN hNI using hex
  refine ⟨N,hN,hNI,?_⟩
  rw [(deterministic_vector_ito_second_moment P B G hG N hN hNI T hT).2]
  have hi : IntervalIntegrable (fun r => ∑ i,∑ j,(G i j r)^2) volume 0 T :=
    (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => (hG i j).pow 2))).intervalIntegrable _ _
  have hk : Continuous (fun r : ℝ => (Real.exp (-α*(T-r)/m))^2*(∑ j,‖b j‖^2)) := by fun_prop
  calc
    _ ≤ ∫ r in 0..T,(Real.exp (-α*(T-r)/m))^2*(∑ j,‖b j‖^2) := by
      apply intervalIntegral.integral_mono_on hT hi (hk.intervalIntegrable _ _)
      intro r hr
      rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have he : (∑ i,(G i j r)^2)=‖E (T-r) (b j)‖^2 := by
        simp only [EuclideanSpace.real_norm_sq_eq,G]
      rw [he]
      have hb := (E (T-r)).le_opNorm (b j)
      have hop := damped_semigroup_norm_bound Γ α m hm hΓ (T-r) (sub_nonneg.mpr hr.2)
      have hh := hb.trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2
    _ = (∑ j,‖b j‖^2)*(∫ r in 0..T,(Real.exp (-α*(T-r)/m))^2) := by
      rw [intervalIntegral.integral_mul_const,mul_comm]
    _ ≤ (∑ j,‖b j‖^2)*(m/(2*α)) := mul_le_mul_of_nonneg_left
      (small_mass_squared_kernel_bound α m T hα hm hT) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by ring
end Asakura.Chapter8
