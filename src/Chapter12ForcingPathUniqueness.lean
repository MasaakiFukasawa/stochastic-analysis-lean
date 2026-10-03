import Chapter12ForcingSolutionUniqueness

open MeasureTheory Set
open scoped Topology NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem forcing_path_uniqueness {E:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b:E → E) (K:ℝ≥0) (hb:LipschitzWith K b) (T:ℝ) (hT:0≤T)
    (a X Y:C(Icc (0:ℝ) T,E))
    (hX:∀t,X t=a t+∫s in 0..t.val,b (X (projIcc 0 T hT s)))
    (hY:∀t,Y t=a t+∫s in 0..t.val,b (Y (projIcc 0 T hT s))) : X=Y := by
  have hp s (hs:s∈Icc 0 T):projIcc 0 T hT s=⟨s,hs⟩ := Subtype.ext (by simp [projIcc,hs.1,hs.2])
  have hs s (ht:s∈Icc 0 T):X (projIcc 0 T hT s)=
      0+(∫r in 0..s,b (X (projIcc 0 T hT r)))+a (projIcc 0 T hT s) := by
    rw [hp s ht,hX]
    simp only [zero_add]
    exact add_comm _ _
  have hv s (ht:s∈Icc 0 T):Y (projIcc 0 T hT s)=
      0+(∫r in 0..s,b (Y (projIcc 0 T hT r)))+a (projIcc 0 T hT s) := by
    rw [hp s ht,hY]
    simp only [zero_add]
    exact add_comm _ _
  have he := Asakura.Chapter10.time_dependent_solution_causal (fun _ z => b z) K
    (hb.continuous.comp continuous_snd) (fun _ => hb)
    (fun s => X (projIcc 0 T hT s)) (fun s => Y (projIcc 0 T hT s))
    (fun s => a (projIcc 0 T hT s)) (fun s => a (projIcc 0 T hT s))
    (X.continuous.comp continuous_projIcc) (Y.continuous.comp continuous_projIcc)
    0 T hT (fun _ _ => rfl) hs hv
  ext t
  simpa only [hp t.val t.property] using he t.val t.property
end Asakura.Chapter12
#print axioms Asakura.Chapter12.forcing_path_uniqueness
