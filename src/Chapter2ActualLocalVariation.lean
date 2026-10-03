import Chapter2AdaptedGluing
import Chapter2LocalVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The actual space A, including adapted right-continuous increasing
parts. No continuity assumption is imposed. -/
structure AdaptedVariationWitness {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (A : ClosedTime T → Ω → ℝ) : Prop where
  parts : ∃ U V : ClosedTime T → Ω → ℝ,
    (∀ t, Measurable[F t] (U t) ∧ Measurable[F t] (V t)) ∧
    (∀ ω, Monotone (fun t => U t ω) ∧ Monotone (fun t => V t ω)) ∧
    (∀ ω t, ContinuousWithinAt (fun s => U s ω) (Ici t) t ∧
      ContinuousWithinAt (fun s => V s ω) (Ici t) t) ∧
    ∀ t ω, A t ω = U t ω - V t ω

structure AdaptedLocalVariationWitness {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (A : ClosedTime T → Ω → ℝ) : Prop where
  localizers : ∃ τ : ℕ → Ω → ClosedTime T,
    (∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t}) ∧
    (∀ ω, Monotone (fun n => τ n ω)) ∧ (∀ n ω, τ n ω < ⊤) ∧
    (∀ ω t, t < ⊤ → ∃ n, t < τ n ω) ∧
    ∀ n, AdaptedVariationWitness F (fun t ω => A (min (τ n ω) t) ω)

theorem AdaptedLocalVariationWitness.toPathwise
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    {F : ClosedTime T → MeasurableSpace Ω} {A : ClosedTime T → Ω → ℝ}
    (hA : AdaptedLocalVariationWitness F A) : LocalVariationWitness F A := by
  obtain ⟨τ,hs,hm,ht,hc,ha⟩ := hA.localizers
  refine ⟨τ,hs,hm,ht,hc,?_⟩
  intro n ω
  obtain ⟨U,V,_,hUV,_,he⟩ := (ha n).parts
  exact ⟨fun t => U t ω,fun t => V t ω,(hUV ω).1,(hUV ω).2,fun t => he t ω⟩

theorem AdaptedVariationWitness.null_cut
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    {F : ClosedTime T → MeasurableSpace Ω} {A : ClosedTime T → Ω → ℝ}
    (hA : AdaptedVariationWitness F A) (N : Set Ω)
    (hN : ∀ t, MeasurableSet[F t] N) :
    AdaptedVariationWitness F (fun t ω => if ω ∈ N then 0 else A t ω) := by
  classical
  obtain ⟨U,V,hm,hmon,hr,he⟩ := hA.parts
  refine ⟨fun t ω => if ω ∈ N then 0 else U t ω,
    fun t ω => if ω ∈ N then 0 else V t ω,?_,?_,?_,?_⟩
  · intro t
    exact ⟨Measurable.ite (hN t) measurable_const (hm t).1,
      Measurable.ite (hN t) measurable_const (hm t).2⟩
  · intro ω
    by_cases hω : ω ∈ N
    · simp only [if_pos hω]; exact ⟨monotone_const,monotone_const⟩
    · simpa only [if_neg hω] using hmon ω
  · intro ω t
    by_cases hω : ω ∈ N
    · simp only [if_pos hω]; exact ⟨continuousWithinAt_const,continuousWithinAt_const⟩
    · simpa only [if_neg hω] using hr ω t
  · intro t ω
    by_cases hω : ω ∈ N
    · simp [hω]
    · simpa only [if_neg hω] using he t ω

/-- Glue stopped integrals on a single completed null set. The conclusion
retains the adapted Jordan parts required by A_loc, rather than only
pathwise bounded variation. -/
theorem adapted_right_continuous_variation_gluing
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (τ : ℕ → Ω → ClosedTime T)
    (hstop : ∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t})
    (hmono : ∀ ω, Monotone (fun n => τ n ω))
    (htop : ∀ n ω, τ n ω < ⊤)
    (hcofinal : ∀ ω t, t < ⊤ → ∃ n, t < τ n ω)
    (A : ℕ → ClosedTime T → Ω → ℝ)
    (hA : ∀ n, AdaptedVariationWitness F (A n))
    (hcompat : ∀ᵐ ω ∂P, ∀ n k, n ≤ k → ∀ t,
      A k (min (τ n ω) t) ω = A n t ω) :
    ∃ G : ClosedTime T → Ω → ℝ,
      AdaptedLocalVariationWitness F G ∧
      (∀ t, t < ⊤ → Measurable[F t] (G t)) ∧
      (∀ ω t, t < ⊤ → ContinuousWithinAt (fun s => G s ω) (Ici t) t) ∧
      (∀ᵐ ω ∂P, ∀ n t, G (min (τ n ω) t) ω = A n t ω) := by
  classical
  let bad := {ω | ¬ (∀ n k, n ≤ k → ∀ t, A k (min (τ n ω) t) ω = A n t ω)}
  let N := toMeasurable P bad
  have hNz : P N = 0 := by rw [measure_toMeasurable]; exact ae_iff.mp hcompat
  have hNF t := hnull t N (measurableSet_toMeasurable _ _) hNz
  have hnon : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]; simpa only [not_not,Set.setOf_mem_eq] using hNz
  let B := fun n t ω => if ω ∈ N then 0 else A n t ω
  have hB n : AdaptedVariationWitness F (B n) := (hA n).null_cut N hNF
  have hBm n t : Measurable[F t] (B n t) := by
    obtain ⟨U,V,hm,_,_,he⟩ := (hB n).parts
    have heq : B n t = fun ω => U t ω-V t ω := funext (he t)
    rw [heq]; exact (hm t).1.sub (hm t).2
  have hBr n ω t : ContinuousWithinAt (fun s => B n s ω) (Ici t) t := by
    obtain ⟨U,V,_,_,hr,he⟩ := (hB n).parts
    have heq : (fun s => B n s ω) = fun s => U s ω-V s ω := funext (fun s => he s ω)
    rw [heq]; exact (hr ω t).1.sub (hr ω t).2
  have hBc ω n k (hnk : n ≤ k) t : B k (min (τ n ω) t) ω = B n t ω := by
    by_cases hω : ω ∈ N
    · simp [B,hω]
    · have hg : ∀ n k, n ≤ k → ∀ t, A k (min (τ n ω) t) ω = A n t ω := by
        by_contra hn
        exact hω (subset_toMeasurable P bad hn)
      simpa only [B,if_neg hω] using hg n k hnk t
  have hex ω := compatible_stops_glue (fun n => τ n ω) (hmono ω) (fun n => htop n ω)
    (fun t ht => (hcofinal ω t ht).imp (fun n hn => hn.le)) (fun n t => B n t ω) (hBc ω)
  choose G he hs using hex
  refine ⟨fun t ω => G ω t,⟨τ,hstop,hmono,htop,hcofinal,?_⟩,?_,?_,?_⟩
  · intro n
    have heq : (fun t ω => G ω (min (τ n ω) t)) = B n := funext (fun t => funext (fun ω => hs ω n t))
    rw [heq]; exact hB n
  · intro t ht
    exact @glued_value_measurable Ω (F t) (fun n ω => B n t ω)
      (fun n => hBm n t) (fun ω => G ω t) (fun ω => he ω t ht)
  · intro ω t ht
    obtain ⟨n,hn⟩ := hcofinal ω t ht
    apply (hBr n ω t).congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hn)] with s hs'
      simpa only [min_eq_right (le_of_lt hs')] using hs ω n s
    · simpa only [min_eq_right hn.le] using hs ω n t
  · filter_upwards [hnon] with ω hω
    intro n t
    simpa only [B,if_neg hω] using hs ω n t

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.adapted_right_continuous_variation_gluing
