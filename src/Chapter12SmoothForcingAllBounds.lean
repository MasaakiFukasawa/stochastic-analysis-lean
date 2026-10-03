import Chapter12SmoothForcingPathMap
import Chapter12VolterraHigherBounds
import Chapter12InverseHigherBounds
import Chapter12ForcingPathLipschitz

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
universe u
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem smooth_forcing_all_bounds {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀ k : ℕ,1≤k → ∃ C : ℝ≥0,∀ x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T : ℝ) (hT : 0≤T) :
    ∃ S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E),ContDiff ℝ ∞ S ∧
      (∀ q t,S q t=q t+∫ s in 0..t.val,b (S q (projIcc 0 T hT s))) ∧
      ∀k : ℕ,1≤k → ∃C : ℝ,0≤C ∧ ∀q,‖iteratedFDeriv ℝ k S q‖≤C := by
  obtain ⟨S,hS,heq⟩ := smooth_forcing_path_map b hb hbound T hT
  refine ⟨S,hS,heq,?_⟩
  let V := fun f : C(Icc (0:ℝ) T,E) => f-pathPrimitive T hT (continuousMapSuperposition b hb.continuous f)
  have hVs : ContDiff ℝ ∞ V := contDiff_id.sub
    ((pathPrimitive T hT).contDiff.comp (continuousMap_superposition_smooth b hb hbound))
  obtain ⟨L,hL⟩ := hbound 1 le_rfl
  have hLip : LipschitzWith L b := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hb.differentiable (by simp))
    intro x
    have hn : ‖fderiv ℝ b x‖≤(L:ℝ) := by simpa only [norm_iteratedFDeriv_one] using hL x
    exact_mod_cast hn
  have hVbij : Function.Bijective V := volterra_path_bijective T hT (fun _ x => b x) L
    (hb.continuous.comp continuous_snd) (fun _ => hLip) V (fun _ _ => rfl)
  have hr : Function.RightInverse S V := by
    intro q
    ext t
    change S q t-(∫s in 0..t.val,b (S q (projIcc 0 T hT s)))=q t
    rw [heq q t]
    abel
  have hl : Function.LeftInverse S V := by
    intro q
    exact hVbij.1 (hr (V q))
  have hSLip := forcing_path_lipschitz b L hLip T hT S heq
  exact inverse_all_higher_bounds V S hVs hS hl hr (volterra_higher_bounds b hb hbound T hT)
    (Real.exp (((L:ℝ)+1)*T)) (Real.exp_pos _).le
    (fun q => norm_fderiv_le_of_lipschitz ℝ hSLip)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.smooth_forcing_all_bounds
