import Chapter12SuperpositionHigherBounds
import Chapter12ContinuousPathPrimitive
import Chapter12InverseHigherDerivative

open Set
open scoped ContDiff Topology NNReal
namespace Asakura.Chapter12
universe u
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem volterra_higher_bounds {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀ k : ℕ,1≤k → ∃ C : ℝ≥0,∀ x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T : ℝ) (hT : 0≤T) :
    ∀ k : ℕ,2≤k → ∃ C : ℝ,0≤C ∧ ∀x : C(Icc (0:ℝ) T,E),
      ‖iteratedFDeriv ℝ k (fun f : C(Icc (0:ℝ) T,E) =>
        f-pathPrimitive T hT (continuousMapSuperposition b hb.continuous f)) x‖≤C := by
  intro k hk
  obtain ⟨C,hC⟩ := hbound k (by omega)
  let P := pathPrimitive (E:=E) T hT
  let B := continuousMapSuperposition (K:=Icc (0:ℝ) T) b hb.continuous
  have hB : ContDiff ℝ ∞ B := continuousMap_superposition_smooth b hb hbound
  refine ⟨‖P‖*C,by positivity,?_⟩
  intro x
  have he : (fun f : C(Icc (0:ℝ) T,E) => f-P (B f)) = (id : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E))-(P ∘ B) := rfl
  change ‖iteratedFDeriv ℝ k (fun f => f-P (B f)) x‖≤_
  rw [he,iteratedFDeriv_sub_apply (contDiff_id (𝕜:=ℝ) (n:=(k:WithTop ℕ∞))).contDiffAt
    ((P.contDiff.comp hB).of_le (by simp)).contDiffAt]
  obtain ⟨n,rfl⟩ : ∃n,k=n+2 := ⟨k-2,by omega⟩
  rw [identity_higher_derivative_zero,zero_sub,norm_neg,
    P.iteratedFDeriv_comp_left hB.contDiffAt (by simp)]
  exact (P.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_left (superposition_higher_norm_bound b hb hB (n+2) C C.coe_nonneg hC x) (norm_nonneg _))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.volterra_higher_bounds
