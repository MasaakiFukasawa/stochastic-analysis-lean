import FullAuditSignedFunctional
import FullAuditStieltjesWritten

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem signed_integral_absolute_bound
    {S : Type*} [MeasurableSpace S] (ν : SignedMeasure S) (f : S → ℝ)
    (hf : Integrable f ν.totalVariation) :
    |signedIntegralRaw ν f| ≤ ∫ r, |f r| ∂ν.totalVariation := by
  have hp : ν.toJordanDecomposition.posPart ≤ ν.totalVariation := by intro s; exact le_add_right le_rfl
  have hn : ν.toJordanDecomposition.negPart ≤ ν.totalVariation := by intro s; exact le_add_left le_rfl
  have hip := hf.mono_measure hp
  have hin := hf.mono_measure hn
  change |(∫ r, f r ∂ν.toJordanDecomposition.posPart)-(∫ r, f r ∂ν.toJordanDecomposition.negPart)| ≤
    ∫ r, |f r| ∂(ν.toJordanDecomposition.posPart+ν.toJordanDecomposition.negPart)
  rw [integral_add_measure hip.abs hin.abs]
  have h := abs_sub_le (∫ r, f r ∂ν.toJordanDecomposition.posPart) 0 (∫ r, f r ∂ν.toJordanDecomposition.negPart)
  simp only [sub_zero,zero_sub,abs_neg] at h
  exact h.trans (add_le_add (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f (μ := ν.toJordanDecomposition.posPart))
    (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f (μ := ν.toJordanDecomposition.negPart)))

/-- The interval Cauchy-Schwarz assumption gives actual signed-integral
integrability and its real square-root bound, including unbounded f and g. -/
theorem signed_stieltjes_integral_square_bound
    (α β : Measure ℝ) [IsFiniteMeasure α] [IsFiniteMeasure β] (ν : SignedMeasure ℝ)
    (hc : ∀ s t, s ≤ t → |ν (Ioc s t)| ≤ Real.sqrt (α.real (Ioc s t))*Real.sqrt (β.real (Ioc s t)))
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable (fun r => f r^2) α) (hgi : Integrable (fun r => g r^2) β) :
    Integrable (fun r => f r*g r) ν.totalVariation ∧
      |signedIntegralRaw ν (fun r => f r*g r)| ≤
        Real.sqrt (∫ r, f r^2 ∂α)*Real.sqrt (∫ r, g r^2 ∂β) := by
  have h := stieltjes_integral_real_intervals α β ν hc f g hf hg
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (.of_forall fun r => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hgi (.of_forall fun r => sq_nonneg _)] at h
  have hfinite : (ENNReal.ofReal (∫ r, f r^2 ∂α))^(1/2:ℝ)*
      (ENNReal.ofReal (∫ r, g r^2 ∂β))^(1/2:ℝ) < ∞ := by finiteness
  have hfg : Integrable (fun r => f r*g r) ν.totalVariation := by
    refine ⟨(hf.mul hg).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs] using h.trans_lt hfinite
  refine ⟨hfg,(signed_integral_absolute_bound ν _ hfg).trans ?_⟩
  have ht := ENNReal.toReal_mono hfinite.ne h
  rw [← ofReal_integral_eq_lintegral_ofReal hfg.abs (.of_forall fun r => abs_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg fun r => abs_nonneg _),ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow,← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (integral_nonneg fun r => sq_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg fun r => sq_nonneg _)] at ht
  simpa only [← Real.sqrt_eq_rpow] using ht

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_integral_absolute_bound
#print axioms Asakura.Chapter2Complete.signed_stieltjes_integral_square_bound
