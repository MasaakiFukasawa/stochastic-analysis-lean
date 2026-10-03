import Chapter12VectorFamilyCommonFrame
import Chapter12VectorCylinderFiniteSum

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem vector_expr_family_rebasis {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (c : I → VectorCylinderExpr H H) :
    ∃(n:ℕ) (e:Fin (n+1) → H) (u:I → Fin (n+1) → GaussianJet (n+1)),
      Orthonormal ℝ e ∧ ∀i (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤),
      (c i).valueLp P W S hS hcore p hp=gaussianTensorCore H P W S hS hcore p hp (u i) e 0 := by
  let q := fun i => (c i).finiteTerms.length
  let f := fun i (j:Fin (q i)) => ((c i).finiteTerms.get j).1
  let v := fun i (j:Fin (q i)) => ((c i).finiteTerms.get j).2
  obtain ⟨n,e,u,he,hu⟩ := vector_family_common_frame P W q f v
  refine ⟨n,e,u,he,fun i p _ hp => ?_⟩
  rw [vector_expr_finite_sum H P W S hS hcore p hp (c i)]
  apply Lp.ext
  filter_upwards [finite_vector_expr_coe H P W S hS hcore (f i) (v i) p hp,hu i,
    gaussian_tensor_core_coe H P W S hS hcore p hp (u i) e 0] with w hw hr hg
  rw [hw,hr,hg]
  exact (Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin (n+1)))
    (fun j => (u i j).f (fun l => W (e l) w) • e j)).symm
end Asakura.Chapter12
#print axioms Asakura.Chapter12.vector_expr_family_rebasis
