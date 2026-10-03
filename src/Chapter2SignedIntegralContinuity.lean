import Chapter2SignedIntegralEstimate
import Chapter2CovarianceProbabilityBound

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem signed_integral_sub
    {S : Type*} [MeasurableSpace S] (ν : SignedMeasure S) (f g : S → ℝ)
    (hf : Integrable f ν.totalVariation) (hg : Integrable g ν.totalVariation) :
    signedIntegralRaw ν (fun r => f r-g r) = signedIntegralRaw ν f-signedIntegralRaw ν g := by
  have hp : ν.toJordanDecomposition.posPart ≤ ν.totalVariation := by intro s; exact le_add_right le_rfl
  have hn : ν.toJordanDecomposition.negPart ≤ ν.totalVariation := by intro s; exact le_add_left le_rfl
  unfold signedIntegralRaw
  rw [integral_sub (hf.mono_measure hp) (hg.mono_measure hp),
    integral_sub (hf.mono_measure hn) (hg.mono_measure hn)]
  ring

/-- A measurable L2 integrand is integrable for the covariance measure,
with the finite quadratic-variation mass as the second factor. -/
theorem signed_stieltjes_single_integral_bound
    (α β : Measure ℝ) [IsFiniteMeasure α] [IsFiniteMeasure β] (ν : SignedMeasure ℝ)
    (hc : ∀ s t, s ≤ t → |ν (Ioc s t)| ≤ Real.sqrt (α.real (Ioc s t))*Real.sqrt (β.real (Ioc s t)))
    (f : ℝ → ℝ) (hf : Measurable f) (hfi : Integrable (fun r => f r^2) α) :
    Integrable f ν.totalVariation ∧ |signedIntegralRaw ν f| ≤
      Real.sqrt (∫ r, f r^2 ∂α)*Real.sqrt (β.real univ) := by
  have h := signed_stieltjes_integral_square_bound α β ν hc f (fun _ => 1) hf measurable_const
    hfi (by simpa using integrable_const (1:ℝ))
  simpa only [mul_one,one_pow,integral_const,smul_eq_mul] using h

/-- The signed Stieltjes integral passes through probability-L2
approximation. This is the second error term in the manuscript's proof
of the general Ito covariance formula. -/
theorem signed_stieltjes_probability_continuity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α β : Ω → Measure ℝ) (ν : Ω → SignedMeasure ℝ)
    [∀ ω, IsFiniteMeasure (α ω)] [∀ ω, IsFiniteMeasure (β ω)]
    (hc : ∀ᵐ ω ∂P, ∀ s t, s ≤ t → |ν ω (Ioc s t)| ≤
      Real.sqrt ((α ω).real (Ioc s t))*Real.sqrt ((β ω).real (Ioc s t)))
    (J : ℕ → Ω → ℝ → ℝ) (H : Ω → ℝ → ℝ)
    (hJm : ∀ n ω, Measurable (J n ω)) (hHm : ∀ ω, Measurable (H ω))
    (hJ : ∀ n, ∀ᵐ ω ∂P, MemLp (J n ω) 2 (α ω))
    (hH : ∀ᵐ ω ∂P, MemLp (H ω) 2 (α ω))
    (hβ : Measurable (fun ω => (β ω).real univ))
    (he : ∀ δ > 0, Tendsto (fun n => P {ω | δ ≤ ∫ r, (J n ω r-H ω r)^2 ∂α ω}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ |signedIntegralRaw (ν ω) (J n ω)-signedIntegralRaw (ν ω) (H ω)|}) atTop (𝓝 0) := by
  apply covariance_probability_from_square_bound P _ _ (fun ω => (β ω).real univ) hβ _ he ε hε
  intro n
  filter_upwards [hc,hJ n,hH] with ω hcω hj hh
  have hjsq := (memLp_two_iff_integrable_sq hj.aestronglyMeasurable).1 hj
  have hhsq := (memLp_two_iff_integrable_sq hh.aestronglyMeasurable).1 hh
  have hed := hj.sub hh
  have hesq := (memLp_two_iff_integrable_sq hed.aestronglyMeasurable).1 hed
  have hji := (signed_stieltjes_single_integral_bound (α ω) (β ω) (ν ω) hcω _ (hJm n ω) hjsq).1
  have hhi := (signed_stieltjes_single_integral_bound (α ω) (β ω) (ν ω) hcω _ (hHm ω) hhsq).1
  have h := (signed_stieltjes_single_integral_bound (α ω) (β ω) (ν ω) hcω
    (fun r => J n ω r-H ω r) ((hJm n ω).sub (hHm ω)) hesq).2
  rw [signed_integral_sub (ν ω) _ _ hji hhi] at h
  exact h

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_integral_sub
#print axioms Asakura.Chapter2Complete.signed_stieltjes_single_integral_bound
#print axioms Asakura.Chapter2Complete.signed_stieltjes_probability_continuity
