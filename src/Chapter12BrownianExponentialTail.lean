import FullAuditGeometricBrownian
import FullAuditFiniteBrownianHitting
import FullAuditContinuousDoob

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The exponential martingale and the manuscript's continuous Doob
inequality give the Brownian maximum tail, before optimizing its parameter. -/
theorem brownian_linear_hitting_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0) (a z : ℝ) :
    P.real {w | ∃ t : ℝ≥0, t ≤ T ∧ z ≤ a*B t w} ≤ Real.exp (-z+a^2*T/2) := by
  letI : Fact (0 ≤ ((T:ℝ):EReal)) := ⟨by exact_mod_cast T.property⟩
  let ρ := finiteTimeToNNReal T
  let X := fun (t : ClosedTime (T:ℝ)) w => brownianExponential B a (ρ t) w
  let F := fun t : ClosedTime (T:ℝ) => pastSigma B (ρ t)
  have htop : ρ ⊤ = T := by
    apply Subtype.ext
    exact EReal.toReal_coe _
  have hmX t : Measurable[F t] (X t) :=
    (((natural_process_adapted B (ρ t)).const_mul a).sub_const _).exp
  have hi : Integrable (X ⊤) P := by
    simpa only [X,htop,brownianExponential] using (normalized_gaussian_exponential P (B T) T (hB.hasLaw_eval T) a).1
  have hmean : (∫ w, X ⊤ w ∂P) = 1 := by
    simpa only [X,htop,brownianExponential] using (normalized_gaussian_exponential P (B T) T (hB.hasLaw_eval T) a).2
  have hr (w : Ω) : Continuous (fun t => X t w) := by
    change Continuous (fun t => Real.exp (a*B (ρ t) w-a^2*(ρ t:ℝ)/2))
    apply Real.continuous_exp.comp
    exact (((hc w).comp (finite_time_to_nnreal_continuous T)).const_mul a).sub
      ((NNReal.continuous_coe.comp (finite_time_to_nnreal_continuous T)).const_mul (a^2) |>.div_const 2)
  let b := Real.exp (z-a^2*T/2)
  have hb : 0 < b := Real.exp_pos _
  have hd := continuous_doob_weak_written P (Fact.out : 0 ≤ ((T:ℝ):EReal)) F
    ((past_sigma_mono B).comp (finite_time_to_nnreal_mono T))
    (fun t => past_sigma_le B hm (ρ t)) X hmX
    (fun w t => (hr w).continuousAt.continuousWithinAt) hi
    (fun t => ae_of_all P fun w => (Real.exp_pos _).le)
    (fun t => (brownian_exponential_martingale P B hB hm a (ρ t) (ρ ⊤)
      (finite_time_to_nnreal_mono T le_top)).symm.le) b hb
  have hevent : {w | ∃ t : ℝ≥0, t ≤ T ∧ z ≤ a*B t w} ⊆
      {w | ENNReal.ofReal b ≤ ⨆ t, ENNReal.ofReal (X t w)} := by
    rintro w ⟨t,ht,hz⟩
    let s : ClosedTime (T:ℝ) := ⟨(t:ℝ),by exact_mod_cast t.property,by exact_mod_cast ht⟩
    have hs : ρ s = t := by apply Subtype.ext; exact EReal.toReal_coe _
    change ENNReal.ofReal b ≤ ⨆ t, ENNReal.ofReal (X t w)
    apply le_iSup_of_le s
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    change z-a^2*T/2 ≤ a*B (ρ s) w-a^2*(ρ s:ℝ)/2
    rw [hs]
    nlinarith [mul_le_mul_of_nonneg_left (show (t:ℝ) ≤ T from ht) (sq_nonneg a)]
  calc
    _ ≤ P.real {w | ENNReal.ofReal b ≤ ⨆ t, ENNReal.ofReal (X t w)} := measureReal_mono hevent
    _ ≤ b⁻¹*(∫ w, X ⊤ w ∂P) := hd.trans (mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hi (ae_of_all P fun w => (Real.exp_pos _).le)) (inv_nonneg.mpr hb.le))
    _ = Real.exp (-z+a^2*T/2) := by
      rw [hmean,mul_one]
      dsimp only [b]
      rw [← Real.exp_neg]
      congr 1
      ring

end Asakura.Chapter12
