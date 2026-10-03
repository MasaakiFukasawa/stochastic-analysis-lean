import Chapter12GaussianJets
import Chapter12VectorCylinderDifferentiation

open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The finite Gaussian functions used in the moment expansion are in
exactly the original core defining the closed Malliavin derivative. -/
noncomputable def GaussianJet.toCylinder {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {n : ℕ}
    (f : GaussianJet n) (e : Fin n → H) : SmoothCylinder H where
  dim := n
  direction := e
  f := f.f
  df := fderiv ℝ f.f
  smooth := f.smooth
  derivative := fun x => (f.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  growth := f.polynomial_growth
  derivative_measurable := fun i => (f.partial i).smooth.continuous.measurable
  derivative_growth := fun i => (f.partial i).polynomial_growth
  all_derivatives_growth := f.growth

@[simp] theorem GaussianJet.toCylinder_partial {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {n : ℕ}
    (f : GaussianJet n) (e : Fin n → H) (i : Fin n) :
    partialSmoothCylinder (f.toCylinder e) i=(f.partial i).toCylinder e := by
  rfl

noncomputable def gaussianVectorCylinder {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n q : ℕ}
    (f : Fin q → GaussianJet n) (e : Fin n → H) (v : Fin q → E) :
    VectorCylinderExpr H E := .sum q (fun j => .term ((f j).toCylinder e) (v j))

/-- Differentiation of the actual cylinder expression gives the coordinate
partials used in the integration-by-parts expansion. -/
theorem gaussian_vector_differentiate {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n q : ℕ}
    (f : Fin q → GaussianJet n) (e : Fin n → H) (v : Fin q → E) :
    (gaussianVectorCylinder f e v).differentiate=
      .sum q (fun j => gaussianVectorCylinder (fun i => (f j).partial i) e
        (fun i => hilbertPureTensor (e i) (v j))) := by
  simp only [gaussianVectorCylinder,VectorCylinderExpr.differentiate,GaussianJet.toCylinder_partial]
  rfl

end Asakura.Chapter12
