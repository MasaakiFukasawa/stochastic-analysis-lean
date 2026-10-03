import Chapter8ForcedPathStability

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A continuous solution map jointly in the initial value and the forcing
path. Its evaluation is consequently jointly continuous, hence measurable. -/
theorem additive_path_map_exists {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (K : ℝ≥0) (hb : LipschitzWith K b) (T : ℝ) (hT : 0 ≤ T) :
    ∃ S : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E), Continuous S ∧
      ∀ p t,S p t=p.1+(∫ s in 0..t.val,b (S p (projIcc 0 T hT s)))+p.2 t := by
  have hex (p : E × C(Icc (0:ℝ) T,E)) := forced_integral_equation_exists T hT K
    (fun _ x => b x) (hb.continuous.comp continuous_snd) (fun _ => hb)
    (fun t => p.1+p.2 (projIcc 0 T hT t))
    (continuous_const.add (p.2.continuous.comp continuous_projIcc))
  choose X hcX hX using hex
  let S : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E) :=
    fun p => ⟨fun t => X p t.val,(hcX p).comp continuous_subtype_val⟩
  have hproj (t : Icc (0:ℝ) T) : projIcc 0 T hT t.val=t := by
    apply Subtype.ext
    simp [projIcc,t.property.1,t.property.2]
  have hLip : LipschitzWith ⟨2*Real.exp (((K:ℝ)+1)*T),by positivity⟩ S := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [dist_eq_norm,dist_eq_norm]
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    have hs := forced_path_stability b K hb (X p) (X q)
      (fun s => p.2 (projIcc 0 T hT s)) (fun s => q.2 (projIcc 0 T hT s))
      (hcX p) (hcX q) p.1 q.1 T ‖p.2-q.2‖ hT (norm_nonneg _)
      (fun s _ => (p.2-q.2).norm_coe_le_norm _)
      (by intro s hs; rw [hX p s hs]; abel)
      (by intro s hs; rw [hX q s hs]; abel) t.val t.property
    change ‖X p t.val-X q t.val‖ ≤ (2*Real.exp (((K:ℝ)+1)*T))*‖p-q‖
    have h1 : ‖p.1-q.1‖ ≤ ‖p-q‖ := norm_fst_le (p-q)
    have h2 : ‖p.2-q.2‖ ≤ ‖p-q‖ := norm_snd_le (p-q)
    have he := (Real.exp_pos (((K:ℝ)+1)*T)).le
    nlinarith
  refine ⟨S,hLip.continuous,?_⟩
  intro p t
  change X p t.val = _
  rw [hX p t.val t.property,hproj]
  have hi : (∫ s in 0..t.val,b (X p s))=
      ∫ s in 0..t.val,b (S p (projIcc 0 T hT s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 t.val := by simpa only [uIcc_of_le t.property.1] using hs
    have he : (projIcc 0 T hT s).val=s := by
      simp [projIcc,hs'.1,hs'.2.trans t.property.2]
    simp only [S,ContinuousMap.coe_mk,he]
  rw [hi]
  abel

end Asakura.Chapter8
