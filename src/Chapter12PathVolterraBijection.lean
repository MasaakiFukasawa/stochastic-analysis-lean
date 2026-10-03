import Chapter10LinearPathUniqueness

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter12
open Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem volterra_path_bijective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0≤T) (b : ℝ → E → E) (K : ℝ≥0)
    (hbc : Continuous (Function.uncurry b)) (hb : ∀ t,LipschitzWith K (b t))
    (V : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E))
    (hV : ∀ u t,V u t=u t-∫ s in 0..t.val,b s (u (projIcc 0 T hT s))) : Function.Bijective V := by
  have hp s (hs : s∈Icc (0:ℝ) T) : projIcc 0 T hT s=⟨s,hs⟩ :=
    Subtype.ext (by simp [projIcc,hs.1,hs.2])
  constructor
  · intro X Y hXY
    have hsol (u : C(Icc (0:ℝ) T,E)) : ∀ s,s∈Icc 0 T →
        u (projIcc 0 T hT s)=(0:E)+(∫ v in 0..s,b v (u (projIcc 0 T hT v)))+V u (projIcc 0 T hT s) := by
      intro s hs
      rw [hp s hs,hV];abel
    have hu := time_dependent_solution_causal b K hbc hb
      (fun s => X (projIcc 0 T hT s)) (fun s => Y (projIcc 0 T hT s))
      (fun s => V X (projIcc 0 T hT s)) (fun s => V Y (projIcc 0 T hT s))
      (X.continuous.comp continuous_projIcc) (Y.continuous.comp continuous_projIcc)
      0 T hT (fun s _ => congrArg (fun q : C(Icc (0:ℝ) T,E) => q (projIcc 0 T hT s)) hXY)
      (hsol X) (hsol Y)
    ext t
    simpa only [hp t.val t.property] using hu t.val t.property
  · intro q
    obtain ⟨S,hS,hSe⟩ := time_dependent_additive_path_map_exists b K hbc hb T hT
    refine ⟨S (0,q),?_⟩
    ext t
    rw [hV,hSe (0,q) t]
    simp only [zero_add]
    abel
end Asakura.Chapter12
#print axioms Asakura.Chapter12.volterra_path_bijective
