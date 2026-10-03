import Chapter2RightContinuousJordan
import Chapter2StoppedPathVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The total variation of a right-continuous adapted BV process belongs
to A, and its paths are increasing. -/
theorem AdaptedVariationWitness.totalVariation
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    {F : ClosedTime T → MeasurableSpace Ω} {A : ClosedTime T → Ω → ℝ}
    (hA : AdaptedVariationWitness F A) (hF : Monotone F) :
    AdaptedVariationWitness F (fun t ω => pathVariation (fun s => A s ω) t) ∧
      ∀ ω, Monotone (fun t => pathVariation (fun s => A s ω) t) := by
  let V := fun t ω => pathVariation (fun s => A s ω) t
  have hm t : Measurable[F t] (V t) := right_continuous_variation_adapted F hF A hA.adapted hA.right_continuous t
  have hmon ω : Monotone (fun t => V t ω) := path_variation_mono _ (hA.boundedVariation ω)
  have hr ω t : ContinuousWithinAt (fun s => V s ω) (Ici t) t := by
    have he s : variationOnFromTo (fun r => A r ω) univ ⊥ s = V s ω := by
      rw [variationOnFromTo.eq_of_le _ _ bot_le,univ_inter,Icc_bot]; rfl
    have h := (hA.boundedVariation ω).continuousWithinAt_variationOnFromTo_Ici
      (a := (⊥ : ClosedTime T)) (hA.right_continuous ω t)
    have hef : variationOnFromTo (fun s => A s ω) univ ⊥ = (fun s => V s ω) := funext he
    rw [hef] at h
    exact h
  exact ⟨⟨V,fun _ _ => 0,fun t => ⟨hm t,measurable_const⟩,
    fun ω => ⟨hmon ω,monotone_const⟩,fun ω t => ⟨hr ω t,continuousWithinAt_const⟩,
    fun _ _ => (sub_zero _).symm⟩,hmon⟩

/-- Parts (1) and (2) of rep252: actual A_loc membership, adaptedness,
and increasing stopped paths for V and V±A. -/
theorem adapted_local_total_variation
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    {F : ClosedTime T → MeasurableSpace Ω} {A : ClosedTime T → Ω → ℝ}
    (hA : AdaptedLocalVariationWitness F A) (hF : Monotone F) :
    let V := fun t ω => pathVariation (fun s => A s ω) t
    AdaptedLocalVariationWitness F V ∧
      AdaptedLocalVariationWitness F (fun t ω => V t ω+A t ω) ∧
      AdaptedLocalVariationWitness F (fun t ω => V t ω-A t ω) ∧
      ∃ τ : ℕ → Ω → ClosedTime T,
        (∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t}) ∧
        (∀ ω, Monotone (fun n => τ n ω)) ∧ (∀ n ω, τ n ω < ⊤) ∧
        (∀ ω t, t < ⊤ → ∃ n, t < τ n ω) ∧
        ∀ n ω, Monotone (fun t => V (min (τ n ω) t) ω) ∧
          Monotone (fun t => V (min (τ n ω) t) ω+A (min (τ n ω) t) ω) ∧
          Monotone (fun t => V (min (τ n ω) t) ω-A (min (τ n ω) t) ω) := by
  intro V
  obtain ⟨τ,hs,hm,ht,hc,ha⟩ := hA.localizers
  have he n t ω : V (min (τ n ω) t) ω = pathVariation (fun s => A (min (τ n ω) s) ω) t :=
    (path_variation_stopping_identity (fun s => A s ω) (τ n ω) t).symm
  have hV : AdaptedLocalVariationWitness F V := by
    refine ⟨τ,hs,hm,ht,hc,?_⟩
    intro n
    have heq : (fun t ω => V (min (τ n ω) t) ω) =
        fun t ω => pathVariation (fun s => A (min (τ n ω) s) ω) t := funext (fun t => funext (he n t))
    rw [heq]
    exact ((ha n).totalVariation hF).1
  refine ⟨hV,hV.add hA hF,?_,τ,hs,hm,ht,hc,?_⟩
  · simpa only [neg_one_mul,← sub_eq_add_neg] using hV.add (hA.smul (-1)) hF
  · intro n ω
    simp only [he]
    exact ⟨((ha n).totalVariation hF).2 ω,
      path_variation_add_sub_monotone _ ((ha n).boundedVariation ω)⟩

/-- Stopped-remainder identity for local BV paths: no bounded variation
at the unused terminal time is assumed. -/
theorem local_path_variation_stopped_remainder
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    {F : ClosedTime T → MeasurableSpace Ω} {A : ClosedTime T → Ω → ℝ}
    (hA : AdaptedLocalVariationWitness F A) (ω : Ω) (σ t : ClosedTime T) (ht : t < ⊤) :
    pathVariation (fun s => A s ω) t-pathVariation (fun s => A s ω) (min σ t) =
      pathVariation (fun s => A s ω-A (min σ s) ω) t := by
  obtain ⟨τ,_,_,_,hc,ha⟩ := hA.localizers
  obtain ⟨n,hn⟩ := hc ω t ht
  have h := path_variation_stopped_remainder (fun s => A (min (τ n ω) s) ω)
    ((ha n).boundedVariation ω) σ t
  rw [path_variation_stopping_identity (fun s => A s ω) (τ n ω) t,
    path_variation_stopping_identity (fun s => A s ω) (τ n ω) (min σ t),
    min_eq_right hn.le,min_eq_right ((min_le_right σ t).trans hn.le)] at h
  rw [h]
  unfold pathVariation
  congr 1
  apply eVariationOn.congr
  intro s hs
  dsimp only
  rw [min_eq_right (hs.trans hn.le),min_eq_right ((min_le_right σ s).trans (hs.trans hn.le))]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.adapted_local_total_variation
#print axioms Asakura.Chapter2Complete.local_path_variation_stopped_remainder
