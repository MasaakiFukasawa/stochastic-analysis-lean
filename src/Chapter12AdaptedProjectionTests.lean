import Chapter12AdaptedStepDensity
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.Chapter2Complete Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The step tests in the Clark--Ocone proof identify the orthogonal
projection onto the actual progressively measurable subspace of L2(dt × P).
The density hypothesis is supplied by chapter 2 rather than assumed. -/
theorem adapted_projection_from_step_tests
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (hT : 0 < T) [Fact (0 ≤ T)]
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N)
    (u ψ : Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le)))
    (hψ : AEStronglyMeasurable[progressiveSpace F] ψ (P.prod (compactTimeMeasure T hT.le)))
    (htest : ∀ (s t : Icc (0:ℝ) T) (Z : Ω → ℝ), Measurable[F s] Z → MemLp Z ∞ P →
      (∫ z, u z * (Ico s t).indicator (fun _ => Z z.1) z.2
        ∂P.prod (compactTimeMeasure T hT.le)) =
      ∫ z, ψ z * (Ico s t).indicator (fun _ => Z z.1) z.2
        ∂P.prod (compactTimeMeasure T hT.le)) :
    ψ = (condExpL2 ℝ ℝ (progressive_space_le_product F hle) u :
      Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le))) := by
  let μ := P.prod (compactTimeMeasure T hT.le)
  let hm := progressive_space_le_product F hle
  letI : Fact (progressiveSpace F ≤ (inferInstance : MeasurableSpace (Ω × Icc (0:ℝ) T))) := ⟨hm⟩
  let A := lpMeas ℝ ℝ (progressiveSpace F) 2 μ
  let e := lpMeasToLpTrimLie ℝ ℝ 2 μ hm
  let j := A.subtypeL.comp e.symm.toLinearIsometry.toContinuousLinearMap
  let L := (innerSL ℝ (u-ψ)).comp j
  have hzero : L = 0 := by
    apply ContinuousLinearMap.ext_on (time_elementary_span_dense P T hT F hF hle hnull)
    rintro J ⟨s,t,Z,hZ,hZinf,hJ⟩
    have hc : (j J : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[μ]
        (fun z => (Ico s t).indicator (fun _ => Z z.1) z.2) :=
      (lpTrimToLpMeas_ae_eq (𝕜 := ℝ) hm J).trans (ae_eq_of_ae_eq_trim hJ)
    change inner ℝ (u-ψ) (j J) = 0
    rw [inner_sub_left,L2.inner_def,L2.inner_def]
    have hval (v : Lp ℝ 2 μ) :
        (∫ z, inner ℝ (v z) (j J z) ∂μ) =
        ∫ z, v z * (Ico s t).indicator (fun _ => Z z.1) z.2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hc] with z hz
      rw [hz]
      change _ * v z = v z * _
      ring
    rw [hval u,hval ψ,htest s t Z hZ hZinf,sub_self]
  have hmem : ψ ∈ A := hψ
  have hall (v : A) : inner ℝ (u-ψ) (v : Lp ℝ 2 μ) = 0 := by
    have hz := DFunLike.congr_fun hzero (e v)
    change inner ℝ (u-ψ) ((e.symm (e v) : A) : Lp ℝ 2 μ) = 0 at hz
    simpa only [e.symm_apply_apply] using hz
  symm
  exact A.eq_starProjection_of_mem_of_inner_eq_zero hmem (fun v hv => hall ⟨v,hv⟩)

end Asakura.Chapter12
