import Chapter10ForcedPathStability
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A finite-horizon L2 path estimate for the actual linear forced equation,
including a random initial condition. -/
theorem linear_forced_path_memLp {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) (T : ℝ) (hT : 0≤T) (K : ℝ≥0)
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (hAK : ∀ t,‖A t‖≤K)
    (ξ : Ω → E) (hξ : MemLp ξ 2 P)
    (W X : Ω → C(Icc (0:ℝ) T,E)) (hW : MemLp W 2 P)
    (hXm : AEStronglyMeasurable X P)
    (he : ∀ᵐ w ∂P,∀ t : Icc (0:ℝ) T,
      X w t=ξ w+(∫ s in 0..t.val,A s (X w (projIcc 0 T hT s)))+W w t) :
    MemLp X 2 P := by
  have hlip t : LipschitzWith K (A t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact ((A t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hAK t) (norm_nonneg _))
  have hb : ∀ᵐ w ∂P,‖X w‖≤Real.exp (((K:ℝ)+1)*T)*(‖ξ w‖+‖W w‖) := by
    filter_upwards [he] with w hw
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    have hh := time_dependent_forced_path_stability (fun s x => A s x) K
      (hA.comp continuous_fst |>.clm_apply continuous_snd) hlip
      (fun s => X w (projIcc 0 T hT s)) (fun _ => 0)
      (fun s => W w (projIcc 0 T hT s)) (fun _ => 0)
      ((X w).continuous.comp continuous_projIcc) continuous_const
      (ξ w) 0 T ‖W w‖ hT (norm_nonneg _) (by
        intro s hs
        simpa only [sub_zero] using (W w).norm_coe_le_norm (projIcc 0 T hT s))
      (by
        intro s hs
        have hp : projIcc 0 T hT s=⟨s,hs⟩ := Subtype.ext (by simp [projIcc,hs.1,hs.2])
        simpa only [hp] using hw ⟨s,hs⟩)
      (by intro s hs; simp) t.val t.property
    have hp : projIcc 0 T hT t.val=t := Subtype.ext (by simp [projIcc,t.property.1,t.property.2])
    simpa only [hp,sub_zero] using hh
  exact ((hξ.norm.add hW.norm).const_mul (Real.exp (((K:ℝ)+1)*T))).mono' hXm hb

end Asakura.Chapter10
