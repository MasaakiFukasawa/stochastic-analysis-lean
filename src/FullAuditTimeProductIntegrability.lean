import FullAuditStationaryVariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Uniform second moments on a finite time measure justify the triple
 Fubini interchange used for the covariance representation. -/
theorem time_covariance_product_integrable {Ω I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure I) [IsFiniteMeasure ν] (Z : Ω → I → ℝ)
    (hmZ : Measurable (Function.uncurry Z))
    (hZ : ∀ t, MemLp (fun ω => Z ω t) 2 P)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, (∫ ω, (Z ω t)^2 ∂P) ≤ C) :
    Integrable (fun p : Ω × (I × I) => Z p.1 p.2.1 * Z p.1 p.2.2)
      (P.prod (ν.prod ν)) := by
  let K := fun p : Ω × (I × I) => Z p.1 p.2.1 * Z p.1 p.2.2
  have hm : Measurable K :=
    (hmZ.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hmZ.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hp (p : I × I) : Integrable (fun ω => K (ω,p)) P := (hZ p.1).integrable_mul (hZ p.2)
  have hnorm (p : I × I) : (∫ ω, ‖K (ω,p)‖ ∂P) ≤ C := by
    have hsq (t : I) : Integrable (fun ω => (Z ω t)^2) P :=
      (memLp_two_iff_integrable_sq (hZ t).aestronglyMeasurable).mp (hZ t)
    have h := integral_mono (hp p).norm ((hsq p.1).add (hsq p.2) |>.div_const 2)
      (fun ω => by
        dsimp only [K,Pi.add_apply]
        rw [Real.norm_eq_abs,abs_mul]
        nlinarith [sq_nonneg (|Z ω p.1|-|Z ω p.2|),sq_abs (Z ω p.1),sq_abs (Z ω p.2)])
    simp only [Pi.add_apply] at h
    rw [integral_div,integral_add (hsq p.1) (hsq p.2)] at h
    linarith [hbound p.1,hbound p.2]
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hp,?_⟩
  have hmem : MemLp (fun p : I × I => ∫ ω, ‖K (ω,p)‖ ∂P) 2 (ν.prod ν) :=
    MemLp.of_bound hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable C (by
      apply ae_of_all _
      intro p
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun ω => norm_nonneg _))]
      exact hnorm p)
  exact hmem.integrable (by norm_num)

/-- With the product integrability now proved, only the actual stationary
 covariance law and the second moment estimate enter this variance bound. -/
theorem stationary_time_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ → ℝ)
    (hmZ : Measurable (Function.uncurry Z)) (hcZ : ∀ ω, Continuous (Z ω))
    (hZ : ∀ t, MemLp (fun ω => Z ω t) 2 P)
    (hmean : ∀ t, (∫ ω, Z ω t ∂P) = 0)
    (c : ℝ → ℝ) (hc : Continuous c) (C κ T : ℝ)
    (hC : 0 ≤ C) (hκ : 0 < κ) (hT : 0 < T)
    (hsecond : ∀ t, (∫ ω, (Z ω t)^2 ∂P) ≤ C)
    (hcov : ∀ s ≥ 0, ∀ t ≥ 0,
      cov[fun ω => Z ω s,fun ω => Z ω t;P] = c |t-s|)
    (hdecay : ∀ u ∈ Icc 0 T, |c u| ≤ C*Real.exp (-κ*u)) :
    (∫ ω, (timeAverage (Z ω) T)^2 ∂P) ≤ 2*C/(κ*T) := by
  have hi := time_covariance_product_integrable P (volume.restrict (Ioc 0 T)) Z hmZ hZ C hC hsecond
  rw [stationary_time_average_variance P Z hcZ hZ hmean c hc T hT hcov hi]
  exact integrated_covariance_bound c C κ T hC hκ hT (hc.intervalIntegrable 0 T) hdecay

end Asakura.FullAudit
