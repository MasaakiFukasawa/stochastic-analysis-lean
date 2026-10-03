import Chapter2LocalPositiveIntegral
import Chapter2SignedDifferenceIntegral
import Chapter2SignedCumulativeVariation
import Chapter2AdaptedVariationAlgebra

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the local signed Stieltjes integral from its two increasing
parts. Membership in the actual A_loc is proved, and the integral is
identified with the decomposition-independent signed integral. -/
theorem local_signed_stieltjes_integral_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (U V : Ω → ℝ → ℝ)
    (hU : ∀ n ω, MonotoneOn (U ω) (Icc 0 (c n)))
    (hV : ∀ n ω, MonotoneOn (V ω) (Icc 0 (c n)))
    (hrU : ∀ n ω r, r ∈ Icc 0 (c n) → ContinuousWithinAt (U ω) (Icc 0 (c n) ∩ Ici r) r)
    (hrV : ∀ n ω r, r ∈ Icc 0 (c n) → ContinuousWithinAt (V ω) (Icc 0 (c n) ∩ Ici r) r)
    (hmU : ∀ n (r : Icc (0:ℝ) (c n)), Measurable[F (realTimeClamp r.val)] (fun ω => U ω r.val))
    (hmV : ∀ n (r : Icc (0:ℝ) (c n)), Measurable[F (realTimeClamp r.val)] (fun ω => V ω r.val))
    (H : Ω × ℝ → ℝ)
    (hH : ∀ n, @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val))) :
    let α := fun n ω => (intervalStieltjes 0 (c n) (hc n) (U ω) (hU n ω) (hrU n ω)).measure
    let β := fun n ω => (intervalStieltjes 0 (c n) (hc n) (V ω) (hV n ω) (hrV n ω)).measure
    (∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (α n ω+β n ω)) →
    ∃ (ξ : ℕ → Ω → SignedMeasure ℝ) (I : ClosedTime T → Ω → ℝ),
      AdaptedLocalVariationWitness F I ∧
      (∀ n ω s t, s ≤ t → ξ n ω (Ioc s t) =
        (U ω (intervalClamp 0 (c n) (hc n) t)-V ω (intervalClamp 0 (c n) (hc n) t))-
        (U ω (intervalClamp 0 (c n) (hc n) s)-V ω (intervalClamp 0 (c n) (hc n) s))) ∧
      (∀ n ω, (ξ n ω).totalVariation ≤ α n ω+β n ω) ∧
      (∀ᵐ ω ∂P, ∀ n t, I (min (realTimeClamp (c n)) t) ω =
        signedCumulative (ξ n ω) (fun r => H (ω,r)) (finitePrefixTime (c n) (hc n) t).val) := by
  intro α β hi
  letI : ∀ n ω, IsFiniteMeasure (α n ω) := fun n ω => intervalStieltjes_finite _ _ _ _ _ _
  letI : ∀ n ω, IsFiniteMeasure (β n ω) := fun n ω => intervalStieltjes_finite _ _ _ _ _ _
  have hiU n : ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (α n ω) :=
    (hi n).mono (fun ω hω => (integrable_add_measure.mp hω).1)
  have hiV n : ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (β n ω) :=
    (hi n).mono (fun ω hω => (integrable_add_measure.mp hω).2)
  obtain ⟨IU,hIU,heU⟩ := local_positive_stieltjes_integral_constructed P F hF hnull c hc hcm hcT hcc
    U hU hrU hmU H hH hiU
  obtain ⟨IV,hIV,heV⟩ := local_positive_stieltjes_integral_constructed P F hF hnull c hc hcm hcT hcc
    V hV hrV hmV H hH hiV
  let ξ : ℕ → Ω → SignedMeasure ℝ := fun n ω => (α n ω).toSignedMeasure-(β n ω).toSignedMeasure
  refine ⟨ξ,fun t ω => IU t ω-IV t ω,?_,?_,?_,?_⟩
  · simpa only [neg_one_mul,← sub_eq_add_neg] using hIU.add (hIV.smul (-1)) hF
  · intro n ω s t hst
    change ((α n ω).toSignedMeasure-(β n ω).toSignedMeasure) (Ioc s t) = _
    rw [VectorMeasure.sub_apply,Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
      Measure.toSignedMeasure_apply_measurable measurableSet_Ioc]
    rw [intervalStieltjes_Ioc_real 0 (c n) (hc n) (U ω) (hU n ω) (hrU n ω) s t hst,
      intervalStieltjes_Ioc_real 0 (c n) (hc n) (V ω) (hV n ω) (hrV n ω) s t hst]
    ring
  · intro n ω
    exact signed_difference_variation_le (α n ω) (β n ω)
  · filter_upwards [heU,heV,ae_all_iff.mpr hi] with ω hUω hVω hiω
    intro n t
    rw [hUω n t,hVω n t,signedCumulative]
    rw [signed_difference_integral (α n ω) (β n ω) _ ((hiω n).indicator measurableSet_Iic)]
    simp only [integral_indicator measurableSet_Iic]
    rfl

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_signed_stieltjes_integral_constructed
