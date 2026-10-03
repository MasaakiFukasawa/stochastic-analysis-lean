import FullAuditVariationStopping

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Subtracting a constant does not change the actual partition variation. -/
theorem variation_sub_constant {ι : Type*} [LinearOrder ι]
    (f : ι → ℝ) (c : ℝ) (S : Set ι) :
    eVariationOn (fun t => f t-c) S = eVariationOn f S := by
  simp only [eVariationOn,edist_sub_right]

/-- The pathwise identity required in part (1) of exercise rep252. A stopping
time may be substituted for a separately fixed path's cut point. -/
theorem path_variation_stopped_remainder {ι : Type*} [LinearOrder ι] [OrderBot ι]
    (f : ι → ℝ) (hf : BoundedVariationOn f univ) (τ t : ι) :
    pathVariation f t-pathVariation f (min τ t) =
      pathVariation (fun s => f s-f (min τ s)) t := by
  let g := fun s => f s-f (min τ s)
  have hz : eVariationOn g (Iic τ) = 0 := by
    apply (eVariationOn.eq_zero_iff _).mpr
    intro a ha b hb
    simp only [g,min_eq_right ha,min_eq_right hb,sub_self,edist_self]
  by_cases ht : t ≤ τ
  · rw [min_eq_right ht,sub_self]
    have hg : eVariationOn g (Iic t) = 0 := by
      exact le_antisymm ((eVariationOn.mono g (Iic_subset_Iic.mpr ht)).trans_eq hz) bot_le
    change 0 = (eVariationOn g (Iic t)).toReal
    rw [hg,ENNReal.toReal_zero]
  · have htt : τ ≤ t := (not_le.mp ht).le
    have hsplit (u : ι → ℝ) : eVariationOn u (Iic τ)+eVariationOn u (Icc τ t) = eVariationOn u (Iic t) := by
      simpa only [univ_inter,Icc_bot] using
        eVariationOn.Icc_add_Icc u (s := univ) (a := ⊥) bot_le htt (mem_univ τ)
    have hseg : eVariationOn g (Icc τ t) = eVariationOn f (Icc τ t) := by
      calc
        eVariationOn g (Icc τ t) = eVariationOn (fun s => f s-f τ) (Icc τ t) :=
          eVariationOn.congr (fun s hs => by simp only [g,min_eq_left hs.1])
        _ = _ := variation_sub_constant f (f τ) _
    have hg : eVariationOn g (Iic t) = eVariationOn f (Icc τ t) := by
      rw [← hsplit g,hz,zero_add,hseg]
    have hs := congrArg ENNReal.toReal (hsplit f)
    rw [ENNReal.toReal_add (hf.mono (subset_univ _)) (hf.mono (subset_univ _))] at hs
    change (eVariationOn f (Iic t)).toReal-(eVariationOn f (Iic (min τ t))).toReal =
      (eVariationOn g (Iic t)).toReal
    rw [min_eq_left htt,hg]
    linarith

/-- The two increasing variation combinations in part (2), from partition
variation rather than an assumed Jordan decomposition. -/
theorem path_variation_add_sub_monotone {ι : Type*} [LinearOrder ι] [OrderBot ι]
    (f : ι → ℝ) (hf : BoundedVariationOn f univ) :
    Monotone (fun t => pathVariation f t+f t) ∧
      Monotone (fun t => pathVariation f t-f t) := by
  have he t : variationOnFromTo f univ ⊥ t = pathVariation f t := by
    rw [variationOnFromTo.eq_of_le _ _ bot_le,univ_inter,Icc_bot]
    rfl
  constructor
  · intro s t hst
    simpa only [Pi.add_apply,he] using
      variationOnFromTo.add_self_monotoneOn hf.locallyBoundedVariationOn (mem_univ (⊥:ι)) (mem_univ s) (mem_univ t) hst
  · intro s t hst
    simpa only [Pi.sub_apply,he] using
      variationOnFromTo.sub_self_monotoneOn hf.locallyBoundedVariationOn (mem_univ (⊥:ι)) (mem_univ s) (mem_univ t) hst

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.path_variation_stopped_remainder
#print axioms Asakura.Chapter2Complete.path_variation_add_sub_monotone
