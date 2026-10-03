import Chapter2WeightedTestIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- The integral on the progressive weighted space is exactly the
expected pathwise Stieltjes integral. This applies in particular to the
pth-power errors of the constructed elementary approximants. -/
theorem weighted_progressive_integral_formula
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) (hab : a ≤ b) [Fact (a ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω x, x ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici x) x)
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (K : ℝ) (hK : ∀ ω, A ω b-A ω a ≤ K)
    (F : Icc a b → MeasurableSpace Ω) (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (H : Ω × Icc a b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (hi : letI : MeasurableSpace (Ω × Icc a b) := progressiveSpace F
      Integrable H ((weightedPathMeasure P a b hab A hA hr hm).trim
        (progressive_space_le_product F hle))) :
    (∫ p, H p ∂(weightedPathMeasure P a b hab A hA hr hm).trim
      (progressive_space_le_product F hle)) =
    ∫ ω, ∫ r, H (ω,projIcc a b hab r)
      ∂(intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure ∂P := by
  let κ := randomStieltjesKernel a b hab A hA hr hm
  letI : IsFiniteKernel κ := random_stieltjes_kernel_finite a b hab A hA hr hm K hK
  let μ := weightedPathMeasure P a b hab A hA hr hm
  let hprog := progressive_space_le_product F hle
  have hip : Integrable H μ := integrable_of_integrable_trim hprog hi
  have hfp : Measurable H := hH.mono hprog le_rfl
  let q : Ω × ℝ → Ω × Icc a b := fun p => (p.1,projIcc a b hab p.2)
  have hq : Measurable q := measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  have hig : Integrable (fun p => H (q p)) (P ⊗ₘ κ) :=
    (integrable_map_measure hfp.aestronglyMeasurable hq.aemeasurable).1 hip
  change (∫ p, H p ∂μ.trim hprog) = _
  rw [← integral_trim (μ := μ) hprog hH.stronglyMeasurable]
  change (∫ p, H p ∂(P ⊗ₘ κ).map q) = _
  rw [integral_map hq.aemeasurable hfp.aestronglyMeasurable,Measure.integral_compProd hig]
  rfl

/-- Integrability of the pathwise integral is also obtained from the
actual product measure, as required by Markov's inequality. -/
theorem weighted_progressive_path_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) (hab : a ≤ b) [Fact (a ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω x, x ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici x) x)
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (K : ℝ) (hK : ∀ ω, A ω b-A ω a ≤ K)
    (F : Icc a b → MeasurableSpace Ω) (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (H : Ω × Icc a b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (hi : letI : MeasurableSpace (Ω × Icc a b) := progressiveSpace F
      Integrable H ((weightedPathMeasure P a b hab A hA hr hm).trim
        (progressive_space_le_product F hle))) :
    Integrable (fun ω => ∫ r, H (ω,projIcc a b hab r)
      ∂(intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure) P := by
  let κ := randomStieltjesKernel a b hab A hA hr hm
  letI : IsFiniteKernel κ := random_stieltjes_kernel_finite a b hab A hA hr hm K hK
  let μ := weightedPathMeasure P a b hab A hA hr hm
  let hprog := progressive_space_le_product F hle
  have hip : Integrable H μ := integrable_of_integrable_trim hprog hi
  have hfp : Measurable H := hH.mono hprog le_rfl
  let q : Ω × ℝ → Ω × Icc a b := fun p => (p.1,projIcc a b hab p.2)
  have hq : Measurable q := measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  have hig : Integrable (fun p => H (q p)) (P ⊗ₘ κ) :=
    (integrable_map_measure hfp.aestronglyMeasurable hq.aemeasurable).1 hip
  exact hig.integral_compProd

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.weighted_progressive_integral_formula

#print axioms Asakura.Chapter2Complete.weighted_progressive_path_integrable
