import Chapter2LocalVariationRealRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false

theorem local_path_variation_continuous
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    {F : ClosedTime T → MeasurableSpace Ω} {A : ClosedTime T → Ω → ℝ}
    (hA : AdaptedLocalVariationWitness F A)
    (hcont : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t) :
    ∀ ω t, t < ⊤ → ContinuousAt (fun s => pathVariation (fun r => A r ω) s) t := by
  obtain ⟨τ,hs,hm,ht,hc,ha⟩ := hA.localizers
  intro ω t htt
  obtain ⟨n,hn⟩ := hc ω t htt
  have hsc : Continuous (fun s => A (min (τ n ω) s) ω) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (hcont ω _ ((min_le_left _ _).trans_lt (ht n ω))).comp
      (continuous_const.min continuous_id).continuousAt
  have hv := (variation_process_continuous _ ((ha n).boundedVariation ω) hsc).continuousAt (x := t)
  apply hv.congr_of_eventuallyEq
  filter_upwards [gt_mem_nhds hn] with s hs'
  change pathVariation (fun r => A r ω) s = pathVariation (fun r => A (min (τ n ω) r) ω) s
  rw [path_variation_stopping_identity (fun r => A r ω) (τ n ω) s,min_eq_right hs'.le]

theorem AdaptedLocalVariationWitness.null_cut
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    {F : ClosedTime T → MeasurableSpace Ω} {A : ClosedTime T → Ω → ℝ}
    (hA : AdaptedLocalVariationWitness F A) (N : Set Ω)
    (hN : ∀ t, MeasurableSet[F t] N) :
    AdaptedLocalVariationWitness F (fun t ω => if ω ∈ N then 0 else A t ω) := by
  obtain ⟨τ,hs,hm,ht,hc,ha⟩ := hA.localizers
  exact ⟨τ,hs,hm,ht,hc,fun n => (ha n).null_cut N hN⟩

/-- A common sample-null set yields continuous paths while retaining
membership in the original A_loc and the same integral at all finite times. -/
theorem local_variation_continuous_representative
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (A : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hc : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → ContinuousAt (fun s => A s ω) t) :
    ∃ B : ClosedTime T → Ω → ℝ, AdaptedLocalVariationWitness F B ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => B s ω) t) ∧
      (∀ᵐ ω ∂P, ∀ t, B t ω = A t ω) := by
  classical
  let bad := {ω | ¬ ∀ t, t < ⊤ → ContinuousAt (fun s => A s ω) t}
  let N := toMeasurable P bad
  have hNz : P N = 0 := by rw [measure_toMeasurable]; exact ae_iff.mp hc
  have hNF t := hnull t N (measurableSet_toMeasurable _ _) hNz
  refine ⟨fun t ω => if ω ∈ N then 0 else A t ω,hA.null_cut N hNF,?_,?_⟩
  · intro ω t ht
    by_cases hω : ω ∈ N
    · simp only [if_pos hω]; exact continuousAt_const
    · have hg : ∀ t, t < ⊤ → ContinuousAt (fun s => A s ω) t := by
        by_contra hn
        exact hω (subset_toMeasurable P bad hn)
      simpa only [if_neg hω] using hg t ht
  · have hn : ∀ᵐ ω ∂P, ω ∉ N := by
      rw [ae_iff]; simpa only [not_not,setOf_mem_eq] using hNz
    exact hn.mono (fun ω hω t => if_neg hω)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_path_variation_continuous
#print axioms Asakura.Chapter2Complete.local_variation_continuous_representative
