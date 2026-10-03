import FullAuditPartitionCE

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit

noncomputable def signedIntegralRaw {Ω : Type*} [MeasurableSpace Ω]
    (ν : SignedMeasure Ω) (f : Ω → ℝ) : ℝ :=
  (∫ ω, f ω ∂ν.toJordanDecomposition.posPart) - (∫ ω, f ω ∂ν.toJordanDecomposition.negPart)

/-- The signed integral is a continuous functional on L1(P) when variation is dominated by cP. -/
noncomputable def signedIntegralOnLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : SignedMeasure Ω) (c : ENNReal) (hc : c ≠ ∞)
    (hdom : ν.totalVariation ≤ c • P) : Lp ℝ 1 P →L[ℝ] ℝ :=
  (L1.integralCLM.comp (Lp.LpToLpOfMeasureLeSMul hc
    ((by
      intro A
      exact le_add_right le_rfl : ν.toJordanDecomposition.posPart ≤ ν.totalVariation).trans hdom))) -
  (L1.integralCLM.comp (Lp.LpToLpOfMeasureLeSMul hc
    ((by
      intro A
      exact le_add_left le_rfl : ν.toJordanDecomposition.negPart ≤ ν.totalVariation).trans hdom)))

/-- Connect the functional to the actual positive-minus-negative integrals. -/
theorem signedIntegralOnLp_apply {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : SignedMeasure Ω) (c : ENNReal) (hc : c ≠ ∞)
    (hdom : ν.totalVariation ≤ c • P) (f : Lp ℝ 1 P) :
    signedIntegralOnLp P ν c hc hdom f = signedIntegralRaw ν f := by
  simp only [signedIntegralOnLp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    signedIntegralRaw]
  congr 1 <;> rw [← L1.integral_eq, L1.integral_eq_integral]
  all_goals exact integral_congr_ae (Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _)

/-- Indicators recover the original signed measure. -/
theorem signedIntegralRaw_indicator {Ω : Type*} [MeasurableSpace Ω]
    (ν : SignedMeasure Ω) (A : Set Ω) (hA : MeasurableSet A) :
    signedIntegralRaw ν (A.indicator (fun _ => (1:ℝ))) = ν A := by
  rw [signedIntegralRaw, integral_indicator hA, integral_indicator hA,
    setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  exact (ν.apply_eq_posPart_real_sub_negPart_real hA).symm

/-- Continuity of the signed integral along an L1-convergent sequence. -/
theorem signedIntegralRaw_tendsto_L1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : SignedMeasure Ω) (c : ENNReal) (hc : c ≠ ∞)
    (hdom : ν.totalVariation ≤ c • P) (f : ℕ → Lp ℝ 1 P) (g : Lp ℝ 1 P)
    (hfg : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => signedIntegralRaw ν (f n)) atTop (𝓝 (signedIntegralRaw ν g)) := by
  have h := (signedIntegralOnLp P ν c hc hdom).continuous.continuousAt.tendsto.comp hfg
  simpa only [Function.comp_def, signedIntegralOnLp_apply] using h

/-- The finite-fiber signed-integral formula used in the discrete variation argument. -/
theorem signedIntegralRaw_partitionMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : SignedMeasure Ω) (J : Finpartition (univ : Set Ω))
    (hJ : ∀ E ∈ J.parts, MeasurableSet E) (X : Ω → ℝ) :
    signedIntegralRaw ν (partitionMean P J X) =
      ∑ E ∈ J.parts, ((P.real E)⁻¹ * ∫ ω in E, X ω ∂P) * ν E := by
  classical
  rw [signedIntegralRaw, partitionMean]
  simp only [Finset.sum_apply]
  rw [integral_finset_sum, integral_finset_sum, ← Finset.sum_sub_distrib]
  · apply Finset.sum_congr rfl
    intro E hE
    rw [integral_indicator (hJ E hE), integral_indicator (hJ E hE),
      setIntegral_const, setIntegral_const, ν.apply_eq_posPart_real_sub_negPart_real (hJ E hE)]
    simp only [smul_eq_mul]
    ring
  all_goals intro E hE; exact (integrable_const _).indicator (hJ E hE)

end Asakura.FullAudit
