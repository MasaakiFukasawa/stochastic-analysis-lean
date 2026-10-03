import Chapter5AprioriConstructed

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Subtract the actual decompositions of the two BSDE solutions. -/
theorem bsde_difference_decomposition
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (Y₁ V₁ M₁ Y₂ V₂ M₂ : ClosedTime T → Ω → ℝ)
    (h₁ : SemimartingaleDecomposition P F Y₁ V₁ M₁)
    (h₂ : SemimartingaleDecomposition P F Y₂ V₂ M₂) :
    SemimartingaleDecomposition P F (fun t w => Y₁ t w-Y₂ t w)
      (fun t w => V₁ t w-V₂ t w) (fun t w => M₁ t w-M₂ t w) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [neg_one_mul,sub_eq_add_neg] using h₁.variation.add (h₂.variation.smul (-1)) hF
  · simpa only [neg_one_mul,sub_eq_add_neg] using
      h₁.martingale.add P F hF hle (h₂.martingale.smul P F (-1))
  · intro w t ht
    exact (h₁.continuous w t ht).sub (h₂.continuous w t ht)
  · intro t ht w
    rw [h₁.decomposition t ht w,h₂.decomposition t ht w]
    ring

/-- Linearity identifies the difference martingale as the Brownian
integral of delta Z, rather than assuming this identification. -/
theorem bsde_difference_integral
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (W M₁ M₂ : ClosedTime T → Ω → ℝ) (Z₁ Z₂ : Ω × ℝ → ℝ)
    (h₁ : ItoCovarianceFormula P F W Z₁ M₁) (h₂ : ItoCovarianceFormula P F W Z₂ M₂) :
    ItoCovarianceFormula P F W (fun z => Z₁ z-Z₂ z) (fun t w => M₁ t w-M₂ t w) := by
  simpa only [neg_one_mul,sub_eq_add_neg,add_comm] using h₂.add_smul P F hF hle W M₂ M₁ Z₂ Z₁ h₁ (-1)

/-- The delta_2 f decomposition used by the manuscript follows from the
Lipschitz bound for f¹ alone. -/
theorem bsde_difference_generator_bound
    (f₁ f₂ : ℝ → ℝ → ℝ) (y₁ z₁ y₂ z₂ C : ℝ)
    (hl : |f₁ y₁ z₁-f₁ y₂ z₂| ≤ C*(|y₁-y₂|+|z₁-z₂|)) :
    |f₁ y₁ z₁-f₂ y₂ z₂| ≤ C*(|y₁-y₂|+|z₁-z₂|)+|f₁ y₂ z₂-f₂ y₂ z₂| := by
  exact (abs_sub_le (f₁ y₁ z₁) (f₁ y₂ z₂) (f₂ y₂ z₂)).trans (add_le_add hl le_rfl)

/-- The primitive drift formula also subtracts, with its actual local
integrability conditions checked before using linearity of integration. -/
theorem bsde_difference_drift
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (V₁ V₂ : ClosedTime T → Ω → ℝ) (B₁ B₂ : Ω × ℝ → ℝ)
    (b : ℝ) (hb : 0 ≤ b)
    (h₁ : ∀ᵐ w ∂P, ∀ r ∈ Icc 0 b,V₁ (realTimeClamp r) w = V₁ ⊥ w+(∫ s in 0..r,B₁ (w,s)))
    (h₂ : ∀ᵐ w ∂P, ∀ r ∈ Icc 0 b,V₂ (realTimeClamp r) w = V₂ ⊥ w+(∫ s in 0..r,B₂ (w,s)))
    (i₁ : ∀ᵐ w ∂P,IntervalIntegrable (fun r => B₁ (w,r)) volume 0 b)
    (i₂ : ∀ᵐ w ∂P,IntervalIntegrable (fun r => B₂ (w,r)) volume 0 b) :
    ∀ᵐ w ∂P, ∀ r ∈ Icc 0 b,
      V₁ (realTimeClamp r) w-V₂ (realTimeClamp r) w = V₁ ⊥ w-V₂ ⊥ w+(∫ s in 0..r,B₁ (w,s)-B₂ (w,s)) := by
  filter_upwards [h₁,h₂,i₁,i₂] with w h₁w h₂w i₁w i₂w
  intro r hr
  have hsub : uIcc (0:ℝ) r ⊆ uIcc 0 b := by simpa [uIcc_of_le hr.1,uIcc_of_le hb] using Icc_subset_Icc_right hr.2
  rw [h₁w r hr,h₂w r hr,intervalIntegral.integral_sub (i₁w.mono_set hsub) (i₂w.mono_set hsub)]
  ring

end Asakura.Chapter5
