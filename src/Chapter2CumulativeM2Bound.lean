import Chapter2CumulativeBound
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The pathwise Cauchy-Schwarz bound gives genuine L2 marginals from the
L2 norm on the random-measure product space. -/
theorem cumulative_kernel_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : Kernel Ω ℝ) [IsFiniteKernel κ]
    (K : ℝ) (hK : 0 ≤ K) (hmass : ∀ ω, (κ ω).real univ ≤ K)
    (G : Ω × ℝ → ℝ) (hG : Measurable G) (hG2 : MemLp G 2 (P ⊗ₘ κ))
    (t : ℝ) :
    MemLp (fun ω => ∫ r in Iic t, G (ω,r) ∂κ ω) 2 P ∧
    (∫ ω, (∫ r in Iic t, G (ω,r) ∂κ ω)^2 ∂P) ≤
      K * ∫ p, G p ^ 2 ∂(P ⊗ₘ κ) := by
  have hi : Integrable (fun p => G p ^ 2) (P ⊗ₘ κ) :=
    (memLp_two_iff_integrable_sq hG2.aestronglyMeasurable).1 hG2
  have hf := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).1 hi
  have he : Integrable (fun ω => ∫ r, G (ω,r)^2 ∂κ ω) P := by
    simpa only [Real.norm_eq_abs,abs_sq] using hf.2
  have hsection : ∀ᵐ ω ∂P, MemLp (fun r => G (ω,r)) 2 (κ ω) := by
    filter_upwards [hf.1] with ω hω
    exact (memLp_two_iff_integrable_sq (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).2 hω
  have hn : Measurable (fun ω => ∫ r in Iic t, G (ω,r) ∂κ ω) := by
    have hind : Measurable (fun p : Ω × ℝ => (Iic t).indicator (fun r => G (p.1,r)) p.2) := by
      have heq : (fun p : Ω × ℝ => (Iic t).indicator (fun r => G (p.1,r)) p.2) =
          (Prod.snd ⁻¹' Iic t).indicator G := by
        funext p
        by_cases hp : p.2 ∈ Iic t <;> simp [Set.indicator,hp]
      rw [heq]
      exact hG.indicator (measurableSet_Iic.preimage measurable_snd)
    have h := hind.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
    simpa only [integral_indicator measurableSet_Iic] using h.measurable
  have hb : ∀ᵐ ω ∂P, (∫ r in Iic t, G (ω,r) ∂κ ω)^2 ≤ K * ∫ r, G (ω,r)^2 ∂κ ω := by
    filter_upwards [hsection] with ω hω
    have h := cumulative_integral_square_bound (κ ω) (fun r => G (ω,r)) hω (Iic t)
    simp only [Real.norm_eq_abs,sq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hmass ω) (integral_nonneg fun r => sq_nonneg _))
  have hs : Integrable (fun ω => (∫ r in Iic t, G (ω,r) ∂κ ω)^2) P := by
    apply (he.const_mul K).mono' (hn.pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs,abs_sq] using hω
  refine ⟨(memLp_two_iff_integrable_sq hn.aestronglyMeasurable).2 hs, ?_⟩
  calc
    _ ≤ ∫ ω, K * ∫ r, G (ω,r)^2 ∂κ ω ∂P := integral_mono_ae hs (he.const_mul K) hb
    _ = _ := by rw [integral_const_mul,Measure.integral_compProd hi]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.cumulative_kernel_memLp_two
