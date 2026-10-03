import Chapter2WeightedHilbert
import Chapter2ProgressiveElementary

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- Elementary integrands with an essentially bounded past-measurable
coefficient belong to the actual progressive L2 space. -/
theorem weighted_elementary_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) (hab : a ≤ b) [Fact (a ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω x, x ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici x) x)
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (K : ℝ) (hK : ∀ ω, A ω b-A ω a ≤ K)
    (F : Icc a b → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (s t : Icc a b) (Z : Ω → ℝ) (hZ : Measurable[F s] Z) (hZinf : MemLp Z ∞ P) :
    letI : MeasurableSpace (Ω × Icc a b) := progressiveSpace F
    MemLp (fun p : Ω × Icc a b => (Ico s t).indicator (fun _ => Z p.1) p.2) 2
      ((weightedPathMeasure P a b hab A hA hr hm).trim (progressive_space_le_product F hle)) := by
  let κ := randomStieltjesKernel a b hab A hA hr hm
  letI : IsFiniteKernel κ := random_stieltjes_kernel_finite a b hab A hA hr hm K hK
  let μ := weightedPathMeasure P a b hab A hA hr hm
  letI : IsFiniteMeasure μ := weighted_path_measure_finite P a b hab A hA hr hm K hK
  let hprog := progressive_space_le_product F hle
  let E := fun p : Ω × Icc a b => (Ico s t).indicator (fun _ => Z p.1) p.2
  have hE := progressive_elementary_measurable a b F hF s t Z hZ
  have hEp : Measurable E := hE.mono hprog le_rfl
  have hs : eLpNormEssSup Z P < ∞ := by
    rw [← eLpNorm_exponent_top hZinf.aestronglyMeasurable]
    exact hZinf.eLpNorm_lt_top
  obtain ⟨C,hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.1 hs
  have hbound : ∀ᵐ p ∂μ, ‖E p‖ ≤ (C:ℝ) := by
    have hq : Measurable (fun p : Ω × ℝ => (p.1,projIcc a b hab p.2)) :=
      measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
    apply (ae_map_iff hq.aemeasurable (measurableSet_le hEp.norm measurable_const)).2
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_le (hEp.comp hq).norm measurable_const)
    filter_upwards [hC] with ω hω
    exact .of_forall fun r => by
      by_cases ht : projIcc a b hab r ∈ Ico s t
      · change ‖(Ico s t).indicator (fun _ => Z ω) (projIcc a b hab r)‖ ≤ (C:ℝ)
        rw [indicator_of_mem ht]
        exact_mod_cast hω
      · change ‖(Ico s t).indicator (fun _ => Z ω) (projIcc a b hab r)‖ ≤ (C:ℝ)
        rw [indicator_of_notMem ht,norm_zero]
        exact C.property
  have hbtrim : ∀ᵐ p ∂μ.trim hprog, ‖E p‖ ≤ (C:ℝ) := by
    rw [ae_iff] at hbound ⊢
    rw [trim_measurableSet_eq hprog]
    · exact hbound
    · letI : MeasurableSpace (Ω × Icc a b) := progressiveSpace F
      exact (measurableSet_le hE.norm measurable_const).compl
  letI : MeasurableSpace (Ω × Icc a b) := progressiveSpace F
  exact MemLp.of_bound hE.aestronglyMeasurable (C:ℝ) hbtrim

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.weighted_elementary_memLp_two
