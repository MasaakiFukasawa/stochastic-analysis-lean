import Chapter2LocalVariationRegularity
import Chapter2VariationStoppedRemainder

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

theorem path_variation_stopping_identity {ι : Type*} [LinearOrder ι] [OrderBot ι]
    (f : ι → ℝ) (τ t : ι) :
    pathVariation (fun s => f (min τ s)) t = pathVariation f (min τ t) := by
  have he : (fun s => min τ s) '' Iic t = Iic (min τ t) := by
    ext s
    constructor
    · rintro ⟨r,hr,rfl⟩; exact min_le_min_left _ hr
    · intro hs
      exact ⟨s,hs.trans (min_le_right _ _),min_eq_right (hs.trans (min_le_left _ _))⟩
  unfold pathVariation
  rw [← he]
  congr 1
  exact eVariationOn.comp_eq_of_monotoneOn f (fun s => min τ s)
    (t := Iic t) (fun _ _ _ _ h => min_le_min_left _ h)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.path_variation_stopping_identity
