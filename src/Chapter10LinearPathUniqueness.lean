import Chapter10LinearCausality
import Chapter10AdditivePathMap

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma linear_forced_paths_unique {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K)
    (T : ℝ) (hT : 0≤T) (p : E × C(Icc (0:ℝ) T,E))
    (X Y : C(Icc (0:ℝ) T,E))
    (hX : ∀ t,X t=p.1+(∫ s in 0..t.val,A s (X (projIcc 0 T hT s)))+p.2 t)
    (hY : ∀ t,Y t=p.1+(∫ s in 0..t.val,A s (Y (projIcc 0 T hT s)))+p.2 t) : X=Y := by
  have hb : ∀ s,LipschitzWith K (A s) := by
    intro s
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hAK s) (norm_nonneg _))
  have hc : Continuous (Function.uncurry fun s x => A s x) := (hA.comp continuous_fst).clm_apply continuous_snd
  have hp s (hs : s∈Icc (0:ℝ) T) : projIcc 0 T hT s=⟨s,hs⟩ :=
    Subtype.ext (by simp [projIcc,hs.1,hs.2])
  have hu := time_dependent_solution_causal (fun s x => A s x) K hc hb
    (fun s => X (projIcc 0 T hT s)) (fun s => Y (projIcc 0 T hT s))
    (fun s => p.2 (projIcc 0 T hT s)) (fun s => p.2 (projIcc 0 T hT s))
    (X.continuous.comp continuous_projIcc) (Y.continuous.comp continuous_projIcc)
    p.1 T hT (fun _ _ => rfl)
    (fun s hs => by simpa only [hp s hs] using hX ⟨s,hs⟩)
    (fun s hs => by simpa only [hp s hs] using hY ⟨s,hs⟩)
  ext t
  simpa only [hp t.val t.property] using hu t.val t.property

end Asakura.Chapter10
