import Chapter12IteratedCylinderExpressions

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem scalar_gradient_expression {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (c : SmoothCylinder H) :
    (cylinderFirstGradientExpr c).valueLp P W S hS hcore p hp=c.gradientLp P W S hS hcore p hp := by
  let C := fun j => (partialSmoothCylinder c j).valueLp P W S hS hcore p hp
  let L := fun j => (ContinuousLinearMap.id ℝ ℝ).smulRight (c.direction j)
  have hc (j : Fin c.dim) : (C j : Ω → ℝ) =ᵐ[P] (partialSmoothCylinder c j).value P W :=
    ((partialSmoothCylinder c j).value_memLp P W S hS hcore p hp).coeFn_toLp
  have hl (j : Fin c.dim) := (L j).coeFn_compLp (C j)
  apply Lp.ext
  filter_upwards [(c.gradient_memLp P W S hS hcore p hp).coeFn_toLp,
    ae_all_iff.mpr hc,ae_all_iff.mpr hl,Lp.coeFn_fun_finsetSum Finset.univ (fun j => (L j).compLp (C j))]
    with w hgrad hval hlin hsum
  change (∑ j,(L j).compLp (C j)) w=c.gradientLp P W S hS hcore p hp w
  change c.gradientLp P W S hS hcore p hp w=c.gradient P W w at hgrad
  rw [hsum,hgrad]
  apply Finset.sum_congr rfl
  intro j _
  rw [hlin j,hval j]
  simp only [L,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply]
  congr 1
  change (partialSmoothCylinder c j).f (fun i => W (c.direction i) w)=
    c.df (fun i => W (c.direction i) w) (Pi.single j 1)
  rw [partialSmoothCylinder_function]
  rfl

end Asakura.Chapter12
