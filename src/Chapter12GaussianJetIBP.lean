import Chapter12GaussianJetAlgebra

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The repeated-IBP step now uses only actual smooth coordinate
functions. Every derivative and every integrability hypothesis is discharged. -/
theorem gaussian_jet_product_ibp {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (f : J → GaussianJet (n+1)) (u : Fin (n+1) → GaussianJet (n+1)) :
    (∫ z : Fin (n+1) → ℝ,(∏ j,(f j).f z)*(GaussianJet.divergence u).f z
      ∂Measure.pi fun _ => gaussianReal 0 1)=
    ∑ j : J,∫ z : Fin (n+1) → ℝ,(∏ l∈Finset.univ.erase j,(f l).f z)*
      (∑ i,(u i).f z*((f j).partial i).f z)
      ∂Measure.pi fun _ => gaussianReal 0 1 := by
  have hh := gaussian_divergence_product_ibp (fun j => (f j).f)
    (fun j i => ((f j).partial i).f) (fun i => (u i).f) (fun i => ((u i).partial i).f)
    (fun j => (f j).coordinate_derivative) (fun i => (u i).coordinate_derivative i)
    (fun j => (f j).smooth.continuous.measurable) (fun j => (f j).polynomial_growth)
    (fun j i => ((f j).partial i).smooth.continuous.measurable)
    (fun j i => ((f j).partial i).polynomial_growth)
    (fun i => (u i).smooth.continuous.measurable) (fun i => (u i).polynomial_growth)
    (fun i => ((u i).partial i).smooth.continuous.measurable)
    (fun i => ((u i).partial i).polynomial_growth)
  simpa only [GaussianJet.divergence_apply] using hh

end Asakura.Chapter12
