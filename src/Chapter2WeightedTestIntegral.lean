import Chapter2WeightedElementary
import Chapter2StieltjesRestriction
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Identify elementary inner-product tests in the progressive Hilbert
space with the expected pathwise Stieltjes integrals used in the proof. -/
theorem weighted_elementary_test_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) (hab : a ≤ b) [Fact (a ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω x, x ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici x) x)
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (K : ℝ) (hK : ∀ ω, A ω b-A ω a ≤ K)
    (F : Icc a b → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (s t : Icc a b) (Z : Ω → ℝ) (hZ : Measurable[F s] Z) (hZinf : MemLp Z ∞ P)
    (H : Ω × Icc a b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (hH2 : letI : MeasurableSpace (Ω × Icc a b) := progressiveSpace F
      MemLp H 2 ((weightedPathMeasure P a b hab A hA hr hm).trim
        (progressive_space_le_product F hle))) :
    (∫ p, ((Ico s t).indicator (fun _ => Z p.1) p.2) * H p
      ∂(weightedPathMeasure P a b hab A hA hr hm).trim (progressive_space_le_product F hle)) =
    ∫ ω, ∫ r, ((Ico s.val t.val).indicator (fun _ => Z ω) r) * H (ω,projIcc a b hab r)
      ∂(intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure ∂P := by
  let κ := randomStieltjesKernel a b hab A hA hr hm
  letI : IsFiniteKernel κ := random_stieltjes_kernel_finite a b hab A hA hr hm K hK
  let μ := weightedPathMeasure P a b hab A hA hr hm
  let hprog := progressive_space_le_product F hle
  let E := fun p : Ω × Icc a b => (Ico s t).indicator (fun _ => Z p.1) p.2
  have hE := progressive_elementary_measurable a b F hF s t Z hZ
  have hE2 := weighted_elementary_memLp_two P a b hab A hA hr hm K hK F hF hle s t Z hZ hZinf
  have hi : Integrable (fun p => E p * H p) (μ.trim hprog) := by
    letI : MeasurableSpace (Ω × Icc a b) := progressiveSpace F
    exact hE2.integrable_mul hH2
  have hip : Integrable (fun p => E p * H p) μ := integrable_of_integrable_trim hprog hi
  have hfp : Measurable (fun p => E p * H p) := (hE.mul hH).mono hprog le_rfl
  let q : Ω × ℝ → Ω × Icc a b := fun p => (p.1,projIcc a b hab p.2)
  have hq : Measurable q := measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  have hig : Integrable (fun p => E (q p)*H (q p)) (P ⊗ₘ κ) := (integrable_map_measure hfp.aestronglyMeasurable hq.aemeasurable).1 hip
  change (∫ p, E p * H p ∂μ.trim hprog) = _
  have hfm : @Measurable _ _ (progressiveSpace F) inferInstance (fun p => E p * H p) := hE.mul hH
  rw [← integral_trim (μ := μ) hprog hfm.stronglyMeasurable]
  change (∫ p, E p * H p ∂(P ⊗ₘ κ).map q) = _
  rw [integral_map hq.aemeasurable hfp.aestronglyMeasurable,Measure.integral_compProd hig]
  apply integral_congr_ae
  exact .of_forall fun ω => by
    apply integral_congr_ae
    filter_upwards [interval_stieltjes_ae_mem_Ioc a b hab (A ω) (hA ω) (hr ω)] with r hr
    have hp : (projIcc a b hab r : ℝ) = r := congrArg Subtype.val (projIcc_of_mem hab ⟨hr.1.le,hr.2⟩)
    have hmemb : projIcc a b hab r ∈ Ico s t ↔ r ∈ Ico s.val t.val := by
      change (s.val ≤ (projIcc a b hab r : ℝ) ∧ (projIcc a b hab r : ℝ) < t.val) ↔ _
      rw [hp]
      rfl
    change ((Ico s t).indicator (fun _ => Z ω) (projIcc a b hab r)) * _ = _
    by_cases hh : r ∈ Ico s.val t.val
    · rw [indicator_of_mem (hmemb.2 hh),indicator_of_mem hh]
    · rw [indicator_of_notMem (fun h => hh (hmemb.1 h)),indicator_of_notMem hh]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.weighted_elementary_test_integral
