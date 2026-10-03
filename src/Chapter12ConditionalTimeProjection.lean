import Chapter12ConditionalPairing
import Chapter12AdaptedProjectionTests

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Whenever the timewise conditional expectations are realized as a
progressive L2 process, they are exactly the joint-space orthogonal projection.
Fubini and the conditional-expectation test identity justify this identification. -/
theorem conditional_time_projection {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0 < T) [Fact (0 ≤ T)]
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet N → P N=0 → MeasurableSet[F t] N)
    (u q : Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le)))
    (hq : AEStronglyMeasurable[progressiveSpace F] q (P.prod (compactTimeMeasure T hT.le)))
    (hcond : ∀ᵐ t ∂compactTimeMeasure T hT.le,
      (fun w => q (w,t)) =ᵐ[P] P[(fun w => u (w,t))|F t]) :
    q = (condExpL2 ℝ ℝ (progressive_space_le_product F hle) u :
      Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le))) := by
  let ν := compactTimeMeasure T hT.le
  apply adapted_projection_from_step_tests P T hT F hF hle hnull u q hq
  intro a b G hGm hG
  have hG2 : MemLp G 2 P := hG.mono_exponent le_top
  have hs : MemLp (fun z : Ω × Icc (0:ℝ) T => (Ico a b).indicator (fun _ => G z.1) z.2)
      2 (P.prod ν) := by
    exact (hG2.comp_fst ν).indicator (measurableSet_Ico.preimage measurable_snd)
  have hu : Integrable (fun z => u z*(Ico a b).indicator (fun _ => G z.1) z.2) (P.prod ν) := (Lp.memLp u).integrable_mul hs
  have hv : Integrable (fun z => q z*(Ico a b).indicator (fun _ => G z.1) z.2) (P.prod ν) := (Lp.memLp q).integrable_mul hs
  rw [integral_prod_symm _ hu,integral_prod_symm _ hv]
  have hsec : ∀ᵐ t ∂ν,MemLp (fun w => u (w,t)) 2 P := by
    filter_upwards [(Lp.memLp u).integrable_sq.prod_left_ae] with t ht
    exact (memLp_two_iff_integrable_sq
      ((Lp.stronglyMeasurable u).measurable.comp measurable_prodMk_right).aestronglyMeasurable).mpr ht
  apply integral_congr_ae
  filter_upwards [hcond,hsec] with t ht hi
  by_cases hab : t ∈ Ico a b
  · simp only [indicator_of_mem hab]
    have he := conditional_raw_pairing P (F t) (hle t) (fun w => u (w,t)) G hi
      (hGm.mono (hF hab.1) le_rfl) hG2
    rw [← he]
    apply integral_congr_ae
    filter_upwards [ht] with w hw
    rw [hw]
  · simp only [indicator_of_notMem hab,mul_zero,integral_zero]

end Asakura.Chapter12
