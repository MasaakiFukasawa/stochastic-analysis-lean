import Chapter12ScalarFromVectorFrame

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem mixed_common_frame {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (f g:SmoothCylinder H) (c d:VectorCylinderExpr H H) :
    ∃(n:ℕ) (e:Fin (n+1) → H) (a b:GaussianJet (n+1))
      (u v:Fin (n+1) → GaussianJet (n+1)),Orthonormal ℝ e ∧
      f.value P W=ᵐ[P] (a.toCylinder e).value P W ∧
      g.value P W=ᵐ[P] (b.toCylinder e).value P W ∧
      ∀(p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤),
        c.valueLp P W S hS hcore p hp=gaussianTensorCore H P W S hS hcore p hp u e 0 ∧
        d.valueLp P W S hS hcore p hp=gaussianTensorCore H P W S hS hcore p hp v e 0 := by
  obtain ⟨h,hh⟩ := exists_norm_eq H (show (0:ℝ)≤1 by norm_num)
  let rows : Fin 4 → VectorCylinderExpr H H :=
    fun i => if i=0 then .term f h else if i=1 then .term g h else if i=2 then c else d
  obtain ⟨n,e,u,he,hu⟩ := vector_expr_family_rebasis H P W S hS hcore rows
  refine ⟨n,e,gaussianVectorScalarProjection (u 0) e h,gaussianVectorScalarProjection (u 1) e h,u 2,u 3,he,?_,?_,?_⟩
  · apply scalar_from_vector_frame H P W S hS hcore f h hh (u 0) e 2 (by simp)
    simpa [rows] using hu 0 2 (by simp)
  · apply scalar_from_vector_frame H P W S hS hcore g h hh (u 1) e 2 (by simp)
    simpa [rows] using hu 1 2 (by simp)
  · intro p _ hp
    exact ⟨by simpa [rows] using hu 2 p hp,by simpa [rows] using hu 3 p hp⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.mixed_common_frame
