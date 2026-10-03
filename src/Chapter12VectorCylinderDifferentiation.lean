import Chapter12VectorCylinderExpressions

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

variable {Ω H E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)

theorem vector_cylinder_derivative_finite_sum (c : SmoothCylinder H) (e : E) :
    vectorCylinderDerivative P W S hS hcore c e p hp=
      ∑ j,vectorCylinderValue P W S hS hcore (partialSmoothCylinder c j)
        (hilbertPureTensor (c.direction j) e) p hp := by
  let C := fun j => (partialSmoothCylinder c j).valueLp P W S hS hcore p hp
  let L := fun j => (ContinuousLinearMap.id ℝ ℝ).smulRight (hilbertPureTensor (c.direction j) e)
  have hc (j : Fin c.dim) : (C j : Ω → ℝ) =ᵐ[P] (partialSmoothCylinder c j).value P W :=
    ((partialSmoothCylinder c j).value_memLp P W S hS hcore p hp).coeFn_toLp
  have hl (j : Fin c.dim) := (L j).coeFn_compLp (C j)
  apply Lp.ext
  filter_upwards [(tensorRightEmbedding e).coeFn_compLp (c.gradientLp P W S hS hcore p hp),
    (c.gradient_memLp P W S hS hcore p hp).coeFn_toLp,
    ae_all_iff.mpr hc,ae_all_iff.mpr hl,Lp.coeFn_fun_finsetSum Finset.univ (fun j => (L j).compLp (C j))]
    with w hw hgrad hval hlin hsum
  change (tensorRightEmbedding e).compLp (c.gradientLp P W S hS hcore p hp) w=
    (∑ j,(L j).compLp (C j)) w
  change c.gradientLp P W S hS hcore p hp w=c.gradient P W w at hgrad
  rw [hw,hgrad,hsum]
  unfold SmoothCylinder.gradient
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,hlin j,hval j]
  simp only [L,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,tensorRightEmbedding_apply]
  congr 1
  change c.df (fun i => W (c.direction i) w) (Pi.single j 1)=
    (partialSmoothCylinder c j).f (fun i => W (c.direction i) w)
  rw [partialSmoothCylinder_function]
  rfl

/-- The explicit derivative is itself a finite smooth cylinder sum, so
iteration stays in the same core at every tensor order. -/
theorem vector_cylinder_differentiate_value (c : VectorCylinderExpr H E) :
    c.differentiate.valueLp P W S hS hcore p hp=c.gradientLp P W S hS hcore p hp := by
  induction c with
  | term c e =>
    exact (vector_cylinder_derivative_finite_sum P W S hS hcore p hp c e).symm
  | sum n c ih =>
    simp only [VectorCylinderExpr.differentiate,VectorCylinderExpr.valueLp,VectorCylinderExpr.gradientLp,ih]
  | smul a c ih =>
    simp only [VectorCylinderExpr.differentiate,VectorCylinderExpr.valueLp,VectorCylinderExpr.gradientLp,ih]

end Asakura.Chapter12
