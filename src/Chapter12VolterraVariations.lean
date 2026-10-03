import Chapter12PathCompositionDerivatives
import Chapter12ContinuousPathPrimitive
import Chapter12HigherChainLinearSplit

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
universe u
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem volterra_parameter_variations {E G : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T : ℝ) (hT : 0≤T)
    (Q X : G → C(Icc (0:ℝ) T,E)) (hQ : ContDiff ℝ ∞ Q) (hX : ContDiff ℝ ∞ X)
    (heq : ∀z t,X z t=Q z t+∫s in 0..t.val,b (X z (projIcc 0 T hT s)))
    (n : ℕ) (z : G) (v : Fin (n+1) → G) (t : Icc (0:ℝ) T) :
    (iteratedFDeriv ℝ (n+1) X z v) t=(iteratedFDeriv ℝ (n+1) Q z v) t+
      ∫s in 0..t.val,
        (fderiv ℝ b (X z (projIcc 0 T hT s))) ((iteratedFDeriv ℝ (n+1) X z v) (projIcc 0 T hT s))+
          higherChainRemainder (fun y => X y (projIcc 0 T hT s)) b (n+1) z v := by
  let B := continuousMapSuperposition (K:=Icc (0:ℝ) T) b hb.continuous
  let P := pathPrimitive (E:=E) T hT
  have hB : ContDiff ℝ ∞ B := continuousMap_superposition_smooth b hb hbound
  have he : X=Q+(P ∘ (B ∘ X)) := by
    funext y
    ext s
    exact heq y s
  have hd := congrArg (fun f : G → C(Icc (0:ℝ) T,E) => (iteratedFDeriv ℝ (n+1) f z v) t) he
  rw [iteratedFDeriv_add_apply ((hQ.of_le (by simp)).contDiffAt)
      (((P.contDiff.comp (hB.comp hX)).of_le (by simp)).contDiffAt),
    P.iteratedFDeriv_comp_left (hB.comp hX).contDiffAt (by simp)] at hd
  change (iteratedFDeriv ℝ (n+1) X z v) t=(iteratedFDeriv ℝ (n+1) Q z v) t+
    ∫s in 0..t.val,(iteratedFDeriv ℝ (n+1) (B ∘ X) z v) (projIcc 0 T hT s) at hd
  rw [hd]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [B]
  rw [path_composition_derivative b hb.continuous X (hB.comp hX)]
  let ev : C(Icc (0:ℝ) T,E) →L[ℝ] E := ContinuousMap.evalCLM ℝ (projIcc 0 T hT s)
  have hXt : ContDiff ℝ ∞ (fun y => X y (projIcc 0 T hT s)) :=
    ev.contDiff.comp hX
  rw [higher_chain_linear_split _ b hXt hb n z v]
  congr 2
  exact congrArg (fun D => D v)
    (ev.iteratedFDeriv_comp_left hX.contDiffAt (by simp))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.volterra_parameter_variations
