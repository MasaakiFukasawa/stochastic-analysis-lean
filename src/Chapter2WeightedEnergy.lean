import Chapter2WeightedHilbert

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal ProbabilityTheory
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- An element of the actual progressive L2 space has finite pathwise
Stieltjes square integral outside a P-null set. -/
theorem progressive_L2_path_energy_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) (hab : a ≤ b) [Fact (a ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω x, x ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici x) x)
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (K : ℝ) (hK : ∀ ω, A ω b-A ω a ≤ K)
    (F : Icc a b → MeasurableSpace Ω) (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (H : Ω × Icc a b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (hH2 : letI : MeasurableSpace (Ω × Icc a b) := progressiveSpace F
      MemLp H 2 ((weightedPathMeasure P a b hab A hA hr hm).trim
        (progressive_space_le_product F hle))) :
    ∀ᵐ ω ∂P, (∫⁻ r, ENNReal.ofReal (H (ω,projIcc a b hab r) ^ 2)
      ∂(intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure) < ∞ := by
  let μ := weightedPathMeasure P a b hab A hA hr hm
  let hprog := progressive_space_le_product F hle
  have hHp : Measurable H := hH.mono hprog le_rfl
  have hsquare : (∫⁻ p, ENNReal.ofReal (H p ^ 2) ∂μ.trim hprog) < ∞ := by
    letI : MeasurableSpace (Ω × Icc a b) := progressiveSpace F
    have hi := (memLp_two_iff_integrable_sq hH2.aestronglyMeasurable).1 hH2
    rw [← ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun p => sq_nonneg _)]
    exact ENNReal.ofReal_lt_top
  rw [lintegral_trim hprog (hH.pow_const 2).ennreal_ofReal] at hsquare
  rw [weighted_path_lintegral_square P a b hab A hA hr hm K hK H hHp] at hsquare
  let κ := randomStieltjesKernel a b hab A hA hr hm
  letI : IsFiniteKernel κ := random_stieltjes_kernel_finite a b hab A hA hr hm K hK
  have hproj : Measurable (fun p : Ω × ℝ => (p.1,projIcc a b hab p.2)) :=
    measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  exact ae_lt_top (((hHp.pow_const 2).ennreal_ofReal.comp hproj).lintegral_kernel_prod_right' (κ := κ)) hsquare.ne

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.progressive_L2_path_energy_finite
