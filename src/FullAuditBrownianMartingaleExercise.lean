import FullAuditNaturalFiltration
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology NNReal
namespace Asakura.FullAudit

/-- The natural-filtration martingale calculation in the Brownian exercise:
 a centered future increment is independent of the whole past, so its
 conditional expectation is zero. -/
theorem brownian_natural_martingale_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable[m] (B t))
    (s t : ℝ≥0) (hst : s ≤ t) : P[B t | pastSigma B s] =ᵐ[P] B s := by
  let H := MeasurableSpace.comap (fun ω (r : Iic s) => B r.val ω) inferInstance
  letI : MeasurableSpace Ω := m
  have hH : H ≤ m := (Measurable.of_eval (fun r : Iic s => hm r.val)).comap_le
  have hind : IndepFun (fun ω => B t ω-B s ω) (fun ω (r : Iic s) => B r.val ω) P := by
    have h := (hB.indepFun_shift s).comp (measurable_pi_apply (t-s)) measurable_id
    simpa only [Function.comp_def,id_eq,add_tsub_cancel_of_le hst] using h
  have hmD : Measurable[m] (fun ω => B t ω-B s ω) := (hm t).sub (hm s)
  have hmean : (∫ ω, (B t ω-B s ω) ∂P) = 0 := by
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),hB.integral_eval,hB.integral_eval,sub_self]
  have hzero : P[(fun ω => B t ω-B s ω) | H] =ᵐ[P] 0 := by
    have h := condExp_indep_eq hmD.comap_le hH
      (show StronglyMeasurable[MeasurableSpace.comap (fun ω => B t ω-B s ω) inferInstance]
        (fun ω => B t ω-B s ω) from (Measurable.of_comap_le le_rfl).stronglyMeasurable) hind
    simpa only [hmean,Pi.zero_def] using h
  have hhist := past_sigma_history B s
  change pastSigma B s = H at hhist
  rw [← hhist] at hzero
  have hself : P[B s | pastSigma B s] = B s :=
    condExp_of_stronglyMeasurable (past_sigma_le B hm s) (natural_process_adapted B s).stronglyMeasurable
      (hB.integrable_eval s)
  have hsub := condExp_sub (hB.integrable_eval t) (hB.integrable_eval s) (pastSigma B s)
  filter_upwards [hzero,hsub] with ω hz hs
  simp only [Pi.sub_apply,hself,Pi.zero_apply] at hs hz ⊢
  change P[B t-B s | pastSigma B s] ω = 0 at hz
  linarith

/-- The exercise uses the augmented natural filtration; its C2 verification
 was checked separately above. All finite Gaussian moments are included. -/
theorem brownian_martingale_exercise {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable[m] (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (p : ℝ≥0∞) (hpt : p ≠ ∞) :
    (∀ t, Measurable[Asakura.nullAugmentation P (pastSigma B t)] (B t)) ∧
    (∀ t, MemLp (B t) p P) ∧ (∀ ω, Continuous (fun t => B t ω)) ∧
    (∀ s t, s ≤ t → P[B t | Asakura.nullAugmentation P (pastSigma B s)] =ᵐ[P] B s) := by
  refine ⟨natural_augmented_adapted P B hm,?_,hc,?_⟩
  · intro t
    exact (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp hpt
  · intro s t hst
    exact (conditional_null_augmentation P (pastSigma B s) (past_sigma_le B hm s) (B t) (hB.integrable_eval t)).symm.trans
      (brownian_natural_martingale_written P B hB hm s t hst)

end Asakura.FullAudit
