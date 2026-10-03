import Mathlib.Order.CompleteLattice.Basic

open Set
namespace Asakura.Chapter11

/-- Values after a deterministic cap do not affect a capped first hit. -/
theorem capped_infimum_congr {D : Type*} [CompleteLinearOrder D]
    (S U : Set D) (R : D) (he : ∀ t,t<R → (t∈S ↔ t∈U)) :
    min (sInf S) R=min (sInf U) R := by
  apply le_antisymm
  · apply le_min _ (min_le_right _ _)
    apply le_sInf
    intro t ht
    by_cases h : t<R
    · exact (min_le_left _ _).trans (sInf_le ((he t h).mpr ht))
    · exact (min_le_right _ _).trans (le_of_not_gt h)
  · apply le_min _ (min_le_right _ _)
    apply le_sInf
    intro t ht
    by_cases h : t<R
    · exact (min_le_left _ _).trans (sInf_le ((he t h).mp ht))
    · exact (min_le_right _ _).trans (le_of_not_gt h)

end Asakura.Chapter11
