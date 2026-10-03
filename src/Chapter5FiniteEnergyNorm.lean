import Chapter5GeneratorNorm

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

noncomputable def finiteEnergyNorm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (R β : ℝ) (H : Ω × ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ w,(∫ r in 0..R,Real.exp (β*r)*H (w,r)^2) ∂P)

lemma finiteEnergyNorm_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (R β : ℝ) (H : Ω × ℝ → ℝ) :
    0≤finiteEnergyNorm P R β H := Real.sqrt_nonneg _

lemma finiteEnergyNorm_sq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (R β : ℝ) (hR : 0≤R) (H : Ω × ℝ → ℝ) :
    (finiteEnergyNorm P R β H)^2=∫ w,(∫ r in 0..R,Real.exp (β*r)*H (w,r)^2) ∂P :=
  Real.sq_sqrt (integral_nonneg (fun w => intervalIntegral.integral_nonneg hR
    (fun r _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))))

lemma finiteEnergyNorm_toLp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (hH : MemLp H 2 (exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β)) :
    finiteEnergyNorm P R β H=‖hH.toLp H‖ := by
  apply (sq_eq_sq₀ (finiteEnergyNorm_nonneg P R β H) (norm_nonneg _)).mp
  rw [finiteEnergyNorm_sq P R β hR,weighted_realization_norm_sq P R β hR hβ H hHm hH]

/-- The exact unsquared bound used in the perturbation recurrence,
for the manuscript's actual iterated weighted integral norm. -/
theorem finite_energy_generator_norm_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β)
    (Y Z G : Ω × ℝ → ℝ) (hYm : Measurable Y) (hZm : Measurable Z) (hGm : Measurable G)
    (hY : MemLp Y 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hZ : MemLp Z 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hG : MemLp G 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C : ℝ) (hC : 0≤C) (hb : ∀ z,|G z|≤C*(|Y z|+|Z z|)) :
    finiteEnergyNorm P R β G≤C*(finiteEnergyNorm P R β Y+finiteEnergyNorm P R β Z) := by
  have hy := (finite_weighted_memLp_two_iff P R hR β hβ Y hYm).mpr hY
  have hz := (finite_weighted_memLp_two_iff P R hR β hβ Z hZm).mpr hZ
  have hg := (finite_weighted_memLp_two_iff P R hR β hβ G hGm).mpr hG
  rw [finiteEnergyNorm_toLp P R β hR hβ G hGm hg,finiteEnergyNorm_toLp P R β hR hβ Y hYm hy,
    finiteEnergyNorm_toLp P R β hR hβ Z hZm hz]
  exact generator_L2_norm_bound _ Y Z G hy hz hg C hC (ae_of_all _ hb)

end Asakura.Chapter5
