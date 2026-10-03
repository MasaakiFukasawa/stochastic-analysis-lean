import Chapter12SuperpositionSmooth
import Chapter12SmoothGlobalInverse
import Chapter12VolterraLinearInvertibility

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
universe u
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The solution map on continuous forcing paths is C-infinity. Its
inverse is the original integral equation; invertibility of the derivative
is proved from the linear Volterra equation. -/
theorem smooth_forcing_path_map {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀ k : ℕ,1≤k → ∃ C : ℝ≥0,∀ x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T : ℝ) (hT : 0≤T) :
    ∃ S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E),ContDiff ℝ ∞ S ∧
      ∀ q t,S q t=q t+∫ s in 0..t.val,b (S q (projIcc 0 T hT s)) := by
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
  obtain ⟨C,hC⟩ := hbound 2 (by omega)
  have hDLip := bounded_second_derivative_lipschitz b hb C hC
  have hD : ContDiff ℝ ∞ (fderiv ℝ b) := hb.fderiv_right (by simp)
  have hder f : HasFDerivAt V
      ((ContinuousLinearMap.id ℝ C(Icc (0:ℝ) T,E))-
        (pathPrimitive T hT).comp (continuousMapApply (continuousMapSuperposition (fderiv ℝ b) hD.continuous f))) f := by
    have hs := superposition_hasFDerivAt (K:=Icc (0:ℝ) T) b (fderiv ℝ b)
      (fun x => (hb.differentiable (by simp)).differentiableAt.hasFDerivAt) C hDLip f
    have hp := (pathPrimitive (E:=E) T hT).hasFDerivAt.comp f hs
    exact (hasFDerivAt_id f).sub hp

  have hd f : Function.Bijective (fderiv ℝ V f) := by
    rw [(hder f).fderiv]
    exact volterra_linear_bijective T hT _
  obtain ⟨S,hS,_,hSV⟩ := smooth_global_inverse V hVs hVbij hd
  refine ⟨S,hS,?_⟩
  intro q t
  have hh := congrArg (fun f : C(Icc (0:ℝ) T,E) => f t) (hSV q)
  change S q t-(∫ s in 0..t.val,b (S q (projIcc 0 T hT s)))=q t at hh
  exact sub_eq_iff_eq_add.mp hh
end Asakura.Chapter12
#print axioms Asakura.Chapter12.smooth_forcing_path_map
