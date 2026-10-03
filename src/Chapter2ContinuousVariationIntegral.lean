import Chapter2OriginalVariationIntegral
import Chapter2SignedCumulativeContinuity

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem signed_integral_process_continuous
    {T : EReal} [Fact (0 ≤ T)] (d : ℝ) (hd : 0 ≤ d)
    (ξ : SignedMeasure ℝ) [NullSingletonClass ξ.totalVariation]
    (H : ℝ → ℝ) (hi : Integrable H ξ.totalVariation) (I : ClosedTime T → ℝ)
    (he : ∀ t, I (min (realTimeClamp d) t) =
      signedCumulative ξ H (finitePrefixTime d hd t).val)
    (t : ClosedTime T) (ht : t < realTimeClamp d) : ContinuousAt I t := by
  have hc := (signed_cumulative_continuous ξ H hi).comp
    (continuous_subtype_val.comp (finite_prefix_time_continuous (T := T) d hd))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [gt_mem_nhds ht] with s hs
  simpa only [Function.comp_def,min_eq_right hs.le] using he s

/-- Continuous integrators produce continuous A_loc integrals, after one
completed sample-null set is removed. Continuity is deduced from the
constructed atomless variation measures, not assumed for the integral. -/
theorem continuous_local_variation_integral_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (A : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hcont : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t) :
    ∃ κ : ℕ → Ω → Measure ℝ,
      (∀ n ω, IsFiniteMeasure (κ n ω)) ∧
      (∀ n ω, ∀ᵐ r ∂κ n ω, r ∈ Ioc 0 (c n)) ∧
      (∀ n ω s t, s ≤ t → (κ n ω).real (Ioc s t) =
        pathVariation (fun r => A r ω) (realTimeClamp (intervalClamp 0 (c n) (hc n) t))-
        pathVariation (fun r => A r ω) (realTimeClamp (intervalClamp 0 (c n) (hc n) s))) ∧
      ∀ H : Ω × ℝ → ℝ,
        (∀ n, @Measurable _ _
          (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
          (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val))) →
        (∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (κ n ω)) →
        ∃ (ξ : ℕ → Ω → SignedMeasure ℝ) (I : ClosedTime T → Ω → ℝ),
          AdaptedLocalVariationWitness F I ∧
          (∀ ω t, t < ⊤ → ContinuousAt (fun s => I s ω) t) ∧
          (∀ n ω s t, s ≤ t → ξ n ω (Ioc s t) =
            A (realTimeClamp (intervalClamp 0 (c n) (hc n) t)) ω-
            A (realTimeClamp (intervalClamp 0 (c n) (hc n) s)) ω) ∧
          (∀ n ω, (ξ n ω).totalVariation ≤ κ n ω) ∧
          (∀ᵐ ω ∂P, ∀ n t, I (min (realTimeClamp (c n)) t) ω =
            signedCumulative (ξ n ω) (fun r => H (ω,r)) (finitePrefixTime (c n) (hc n) t).val) := by
  obtain ⟨κ,hκ,hsupport,hinc,hatom,hconstruct⟩ := original_local_variation_integral_constructed
    P F hF hnull c hc hcm hcT hcc A hA
  refine ⟨κ,hκ,hsupport,hinc,?_⟩
  intro H hH hi
  obtain ⟨ξ,I,hI,hξ,hdom,he⟩ := hconstruct H hH hi
  have hIc : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → ContinuousAt (fun s => I s ω) t := by
    filter_upwards [he,ae_all_iff.mpr hi] with ω heω hiω
    intro t ht
    obtain ⟨n,hn⟩ := hcc t ht
    letI : NullSingletonClass (κ n ω) := hatom hcont n ω
    letI : NullSingletonClass (ξ n ω).totalVariation :=
      ⟨fun r => le_antisymm (((hdom n ω) {r}).trans_eq (measure_singleton r)) bot_le⟩
    exact signed_integral_process_continuous (c n) (hc n) (ξ n ω) _
      ((hiω n).mono_measure (hdom n ω)) (fun t => I t ω) (heω n) t hn
  obtain ⟨J,hJ,hJc,hJI⟩ := local_variation_continuous_representative P F hnull I hI hIc
  refine ⟨ξ,J,hJ,hJc,hξ,hdom,?_⟩
  filter_upwards [hJI,he] with ω hJω heω
  intro n t
  rw [hJω]
  exact heω n t

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_local_variation_integral_constructed
