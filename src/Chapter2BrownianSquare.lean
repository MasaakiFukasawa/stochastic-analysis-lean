import FullAuditBrownianMartingaleExercise
import Chapter2ElementaryIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology NNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1200000

/-- The second moment is calculated from the Brownian covariance and
zero mean, not supplied as an additional Brownian-motion hypothesis. -/
theorem brownian_square_mean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    (∫ ω, B t ω ^ 2 ∂P) = (t:ℝ) := by
  have h := hB.covariance_eval t t
  simp only [covariance,hB.integral_eval,sub_zero,min_self] at h
  simpa only [pow_two] using h

/-- The calculation identifying Brownian quadratic variation: the
square minus elapsed time is a martingale for the whole natural past. -/
theorem brownian_square_natural_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (s t : ℝ≥0) (hst : s ≤ t) :
    P[(fun ω => B t ω ^ 2-(t:ℝ)) | pastSigma B s] =ᵐ[P]
      (fun ω => B s ω ^ 2-(s:ℝ)) := by
  let F := pastSigma B s
  letI : MeasurableSpace Ω := m
  let D := fun ω => B t ω-B s ω
  have hF : F ≤ m := past_sigma_le B hm s
  have hD2 : MemLp D 2 P := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.sub
    (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hBs2 := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hDt : Integrable D P := hD2.integrable (by norm_num)
  have hDs : Integrable (fun ω => D ω ^ 2) P := (memLp_two_iff_integrable_sq hD2.aestronglyMeasurable).1 hD2
  have hBs : Integrable (fun ω => B s ω ^ 2) P := (memLp_two_iff_integrable_sq hBs2.aestronglyMeasurable).1 hBs2
  have hind : IndepFun D (fun ω (r : Iic s) => B r.val ω) P := by
    have h := (hB.indepFun_shift s).comp (measurable_pi_apply (t-s)) measurable_id
    simpa only [Function.comp_def,id_eq,add_tsub_cancel_of_le hst] using h
  have hmean : (∫ ω, D ω ∂P) = 0 := by
    dsimp only [D]
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),hB.integral_eval,hB.integral_eval,sub_self]
  have hsquare : (∫ ω, D ω ^ 2 ∂P) = (t:ℝ)-(s:ℝ) := by
    have h := brownian_square_mean P _ (hB.shift s) (t-s)
    simpa only [add_tsub_cancel_of_le hst,NNReal.coe_sub hst,D] using h
  have hhist := past_sigma_history B s
  have hDc : P[D | F] =ᵐ[P] (fun _ => (0:ℝ)) := by
    have h := condExp_indep_eq ((hm t).sub (hm s)).comap_le
      (Measurable.of_eval (fun r : Iic s => hm r.val)).comap_le
      (show StronglyMeasurable[MeasurableSpace.comap D inferInstance] D from
        (Measurable.of_comap_le le_rfl).stronglyMeasurable) hind
    rw [← hhist] at h
    simpa only [hmean] using h
  have hDsqc : P[(fun ω => D ω ^ 2) | F] =ᵐ[P] (fun _ => (t:ℝ)-(s:ℝ)) := by
    have hi := hind.comp (measurable_id.pow_const 2) measurable_id
    have h := condExp_indep_eq (((hm t).sub (hm s)).pow_const 2).comap_le
      (Measurable.of_eval (fun r : Iic s => hm r.val)).comap_le
      (show StronglyMeasurable[MeasurableSpace.comap (fun ω => D ω ^ 2) inferInstance]
        (fun ω => D ω ^ 2) from (Measurable.of_comap_le le_rfl).stronglyMeasurable) hi
    simp only [Function.comp_def,id_eq] at h
    rw [← hhist] at h
    simpa only [hsquare] using h
  have hcrossi : Integrable (fun ω => B s ω*D ω) P := hBs2.integrable_mul hD2
  have hcross := condExp_mul_of_stronglyMeasurable_left
    (natural_process_adapted B s).stronglyMeasurable hcrossi hDt
  have hself : P[(fun ω => B s ω ^ 2) | F] = (fun ω => B s ω ^ 2) :=
    condExp_of_stronglyMeasurable hF ((natural_process_adapted B s).pow_const 2).stronglyMeasurable hBs
  have he : (fun ω => B t ω ^ 2-(t:ℝ)) =
      (fun ω => B s ω ^ 2) + (fun ω => 2*(B s ω*D ω)) + (fun ω => D ω ^ 2) - (fun _ => (t:ℝ)) := by
    funext ω
    dsimp only [D,Pi.add_apply,Pi.sub_apply]
    ring
  rw [he]
  have hadd := condExp_add hBs (hcrossi.const_mul 2) F
  have hadd' := condExp_add (hBs.add (hcrossi.const_mul 2)) hDs F
  have hsub := condExp_sub ((hBs.add (hcrossi.const_mul 2)).add hDs) (integrable_const (t:ℝ)) F
  have hconst : P[(fun _ : Ω => (t:ℝ)) | F] = (fun _ => (t:ℝ)) := condExp_const hF (t:ℝ)
  have hscale := condExp_smul (μ := P) (2:ℝ) (fun ω => B s ω*D ω) F
  filter_upwards [hDc,hDsqc,hcross,hadd,hadd',hsub,hscale] with ω hd hds hcr ha ha' hs hsc
  simp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,hself,hconst] at ha ha' hs hsc hcr ⊢
  change P[(fun ω => B s ω*D ω) | F] ω = B s ω * P[D | F] ω at hcr
  rw [hd] at hcr
  simp only [mul_zero] at hcr
  change P[(fun ω => 2*(B s ω*D ω)) | F] ω = 2*P[(fun ω => B s ω*D ω) | F] ω at hsc
  rw [hs,ha',ha,hsc,hcr,hds]
  ring

/-- The square-minus-time martingale identity also holds for the
null-augmented natural filtration used throughout the manuscript. -/
theorem brownian_square_augmented_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (s t : ℝ≥0) (hst : s ≤ t) :
    P[(fun ω => B t ω ^ 2-(t:ℝ)) | Asakura.nullAugmentation P (pastSigma B s)] =ᵐ[P]
      (fun ω => B s ω ^ 2-(s:ℝ)) := by
  have h2 := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hi : Integrable (fun ω => B t ω ^ 2-(t:ℝ)) P :=
    ((memLp_two_iff_integrable_sq h2.aestronglyMeasurable).1 h2).sub (integrable_const _)
  exact (conditional_null_augmentation P (pastSigma B s) (past_sigma_le B hm s)
    _ hi).symm.trans (brownian_square_natural_martingale P B hB hm s t hst)

/-- Gaussian fourth moments give the L2 moments needed to localize the
square-minus-time process in the quadratic-variation exercise. -/
theorem brownian_square_centered_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    MemLp (fun ω => B t ω ^ 2-(t:ℝ)) 2 P := by
  have h4 : MemLp (B t) 4 P := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp (by norm_num)
  have h2 : MemLp (fun ω => B t ω ^ 2) 2 P := by
    have h := h4.norm_rpow_div 2
    norm_num only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] at h
    have he := ENNReal.ofReal_div_of_pos (x := (4:ℝ)) (by norm_num : 0 < (2:ℝ))
    norm_num at he
    rw [← he] at h
    exact h
  exact h2.sub (memLp_const _)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.brownian_square_mean
#print axioms Asakura.Chapter2Complete.brownian_square_natural_martingale

#print axioms Asakura.Chapter2Complete.brownian_square_augmented_martingale
#print axioms Asakura.Chapter2Complete.brownian_square_centered_memLp_two
