import Chapter2AdaptedVariationAlgebra

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
  {F : ClosedTime T → MeasurableSpace Ω} {A : ClosedTime T → Ω → ℝ}

theorem AdaptedVariationWitness.adapted (hA : AdaptedVariationWitness F A) :
    ∀ t, Measurable[F t] (A t) := by
  obtain ⟨U,V,hm,_,_,he⟩ := hA.parts
  intro t
  have h : A t = fun ω => U t ω-V t ω := funext (he t)
  rw [h]; exact (hm t).1.sub (hm t).2

theorem AdaptedVariationWitness.right_continuous (hA : AdaptedVariationWitness F A) :
    ∀ ω t, ContinuousWithinAt (fun s => A s ω) (Ici t) t := by
  obtain ⟨U,V,_,_,hr,he⟩ := hA.parts
  intro ω t
  have h : (fun s => A s ω) = fun s => U s ω-V s ω := funext (fun s => he s ω)
  rw [h]; exact (hr ω t).1.sub (hr ω t).2

theorem AdaptedVariationWitness.boundedVariation (hA : AdaptedVariationWitness F A) :
    ∀ ω, BoundedVariationOn (fun t => A t ω) univ := by
  obtain ⟨U,V,_,hm,_,he⟩ := hA.parts
  intro ω
  have h : (fun t => A t ω) = fun t => U t ω-V t ω := funext (fun t => he t ω)
  rw [h]
  exact increasing_difference_boundedVariation _ _ (hm ω).1 (hm ω).2

theorem AdaptedLocalVariationWitness.adapted (hA : AdaptedLocalVariationWitness F A) :
    ∀ t, t < ⊤ → Measurable[F t] (A t) := by
  obtain ⟨τ,hs,hm,ht,hc,ha⟩ := hA.localizers
  intro t ht'
  apply @glued_value_measurable Ω (F t) (fun n ω => A (min (τ n ω) t) ω)
    (fun n => (ha n).adapted t)
  intro ω
  obtain ⟨n,hn⟩ := hc ω t ht'
  exact eventually_atTop.mpr ⟨n,fun k hk => congrArg (fun s => A s ω)
    (min_eq_right (hn.le.trans (hm ω hk)))⟩

theorem AdaptedLocalVariationWitness.right_continuous (hA : AdaptedLocalVariationWitness F A) :
    ∀ ω t, t < ⊤ → ContinuousWithinAt (fun s => A s ω) (Ici t) t := by
  obtain ⟨τ,hs,hm,ht,hc,ha⟩ := hA.localizers
  intro ω t ht'
  obtain ⟨n,hn⟩ := hc ω t ht'
  apply ((ha n).right_continuous ω t).congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hn)] with s hs
    simp only [min_eq_right hs.le]
  · simp only [min_eq_right hn.le]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.AdaptedLocalVariationWitness.adapted
#print axioms Asakura.Chapter2Complete.AdaptedLocalVariationWitness.right_continuous
