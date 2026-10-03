import Chapter2RandomStieltjes
import Chapter2ProgressiveSpace

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal ProbabilityTheory
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) (hab : a ≤ b) (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω x, x ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici x) x)
    (hm : ∀ t, Measurable (fun ω => A ω t))

/-- The random Stieltjes product measure on the actual compact time
interval. The interval extension is constant outside the interval. -/
noncomputable def weightedPathMeasure : Measure (Ω × Icc a b) :=
  (P ⊗ₘ randomStieltjesKernel a b hab A hA hr hm).map
    (fun p : Ω × ℝ => (p.1,projIcc a b hab p.2))

theorem weighted_path_measure_finite (K : ℝ) (hK : ∀ ω, A ω b-A ω a ≤ K) :
    IsFiniteMeasure (weightedPathMeasure P a b hab A hA hr hm) := by
  letI : IsFiniteKernel (randomStieltjesKernel a b hab A hA hr hm) :=
    random_stieltjes_kernel_finite a b hab A hA hr hm K hK
  exact Measure.isFiniteMeasure_map _ _

/-- The squared integrand norm is precisely the expectation of the
pathwise Stieltjes square integral. This also covers infinite integrals. -/
theorem weighted_path_lintegral_square (K : ℝ) (hK : ∀ ω, A ω b-A ω a ≤ K)
    (H : Ω × Icc a b → ℝ) (hH : Measurable H) :
    (∫⁻ p, ENNReal.ofReal (H p ^ 2) ∂weightedPathMeasure P a b hab A hA hr hm) =
      ∫⁻ ω, ∫⁻ r, ENNReal.ofReal (H (ω,projIcc a b hab r) ^ 2)
        ∂(intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure ∂P := by
  let κ := randomStieltjesKernel a b hab A hA hr hm
  letI : IsFiniteKernel κ := random_stieltjes_kernel_finite a b hab A hA hr hm K hK
  have hproj : Measurable (fun p : Ω × ℝ => (p.1,projIcc a b hab p.2)) :=
    measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  rw [weightedPathMeasure,lintegral_map ((hH.pow_const 2).ennreal_ofReal) hproj]
  exact Measure.lintegral_compProd (((hH.pow_const 2).ennreal_ofReal).comp hproj)

/-- Apply the checked completeness proof to the concrete random measure
and its progressive sigma algebra, as required by the density lemma. -/
theorem weighted_progressive_hilbert_complete
    [Fact (a ≤ b)] (F : Icc a b → MeasurableSpace Ω)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›) :
    letI : MeasurableSpace (Ω × Icc a b) := progressiveSpace F
    CompleteSpace (Lp ℝ 2 ((weightedPathMeasure P a b hab A hA hr hm).trim
      (progressive_space_le_product F hle))) := by
  exact progressive_L2_complete F hle _

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.weighted_path_measure_finite
#print axioms Asakura.Chapter2Complete.weighted_path_lintegral_square
#print axioms Asakura.Chapter2Complete.weighted_progressive_hilbert_complete
