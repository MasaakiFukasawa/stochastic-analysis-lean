import FullAuditBrownianMartingaleExercise
import FullAuditCountableFuture

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace Asakura.FullAudit

noncomputable def finiteFuture {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (J : Finset ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : J → ℝ := fun s => B (t+s.val) ω-B t ω

theorem finite_future_measurable {Ω : Type*} {m : MeasurableSpace Ω}
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable[m] (B t)) (J : Finset ℝ≥0) (t : ℝ≥0) :
    Measurable[m] (finiteFuture B J t) :=
  Measurable.of_eval fun s => (hm (t+s.val)).sub (hm t)

theorem finite_future_continuous {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (J : Finset ℝ≥0) (ω : Ω) :
    Continuous (fun t => finiteFuture B J t ω) := by
  apply continuous_pi
  intro s
  exact ((hc ω).comp (continuous_id.add continuous_const)).sub (hc ω)

/-- Finite-dimensional stationary increment laws determine the mean of each test. -/
theorem brownian_future_test_mean {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (J : Finset ℝ≥0) (t : ℝ≥0) (h : (J → ℝ) → ℝ) (hh : Continuous h) :
    (∫ ω, h (finiteFuture B J t ω) ∂P) = ∫ x, h x ∂BrownianReal.projectiveFamily J := by
  exact ((hB.shift t).hasLaw J).integral_comp hh.aestronglyMeasurable

/-- The deterministic-time independence used on each stopping-time fiber.
The null augmentation is explicitly included. -/
theorem brownian_future_test_conditional {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable[m] (B t))
    (J : Finset ℝ≥0) (t : ℝ≥0) (h : (J → ℝ) → ℝ) (hh : Continuous h)
    (C : ℝ) (hb : ∀ x, ‖h x‖ ≤ C) :
    P[(fun ω => h (finiteFuture B J t ω)) | Asakura.nullAugmentation P (pastSigma B t)] =ᵐ[P]
      fun _ => ∫ x, h x ∂BrownianReal.projectiveFamily J := by
  let U := fun ω => h (finiteFuture B J t ω)
  have hUm : Measurable[m] U := hh.measurable.comp (finite_future_measurable B hm J t)
  have hUi : Integrable U P := Integrable.of_bound hUm.aestronglyMeasurable C (ae_of_all _ fun ω => hb _)
  have hind : IndepFun U (fun ω (r : Iic t) => B r.val ω) P := by
    exact (hB.indepFun_shift t).comp
      (hh.measurable.comp (Measurable.of_eval (fun s : J => measurable_pi_apply s.val))) measurable_id
  have hc := condExp_indep_eq hUm.comap_le
    (Measurable.of_eval (fun r : Iic t => hm r.val)).comap_le
    (show StronglyMeasurable[MeasurableSpace.comap U inferInstance] U from
      (Measurable.of_comap_le le_rfl).stronglyMeasurable) hind
  have hhist := past_sigma_history B t
  rw [← hhist] at hc
  have hmean := brownian_future_test_mean P B hB J t h hh
  change (∫ ω, U ω ∂P) = _ at hmean
  rw [hmean] at hc
  exact (conditional_null_augmentation P _ (past_sigma_le B hm t) U hUi).symm.trans hc
end Asakura.FullAudit
