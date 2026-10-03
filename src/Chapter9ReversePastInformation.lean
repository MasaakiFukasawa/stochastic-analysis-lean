import Chapter9ReverseTransitionFields
import Chapter9ObservationReindex

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The completed information used in the proof is exactly that generated
 by all reversed observations Zᵤ=Xₜ₋ᵤ, 0≤u≤s, in the manuscript. -/
theorem reversed_information_as_past {Ω E : Type*} [m : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : ℝ → Ω → E) (T s : ℝ) :
    reversedNaturalInformation P X T s=nullAugmentedInformation (m := m) P
      (MeasurableSpace.comap (fun w (u : Icc 0 s) => X (T-u) w) MeasurableSpace.pi) := by
  apply congrArg (nullAugmentedInformation (m := m) P)
  apply observation_information_congr (fun r : Icc (T-s) T => X r.val)
    (fun u : Icc 0 s => X (T-u.val))
  · intro r
    refine ⟨⟨T-r.val,by constructor <;> linarith [r.property.1,r.property.2]⟩,?_⟩
    dsimp only
    rw [sub_sub_cancel]
  · intro u
    exact ⟨⟨T-u.val,by constructor <;> linarith [u.property.1,u.property.2]⟩,rfl⟩
end Asakura.Chapter9
