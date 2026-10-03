import Chapter12GaussianCoreSquareTransport
import Chapter12FiniteDivergenceL2

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000

theorem gaussian_tensor_zero_square {N : ℕ} (u : Fin N → GaussianJet N) (x : Fin N → ℝ) :
    gaussianArrayNorm (gaussianTensorJet u 0) x^2=∑ i,(u i).f x^2 := by
  unfold gaussianArrayNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  exact Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin N)) (fun i => (u i).f x^2)

theorem gaussian_tensor_one_square {N : ℕ} (u : Fin N → GaussianJet N) (x : Fin N → ℝ) :
    gaussianArrayNorm (gaussianTensorJet u 1) x^2=∑ i,∑ j,((u j).partial i).f x^2 := by
  unfold gaussianArrayNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 2 => Fin N)),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin N)) (fun j => ((u j).partial i).f x^2)

/-- The sharp square estimate requires only orders zero and one, unlike
the higher-moment estimate. All smoothness and growth inputs are discharged. -/
theorem gaussian_jet_square_bound {n : ℕ} (u : Fin (n+1) → GaussianJet (n+1)) :
    (∫ x,|(GaussianJet.divergence u).f x|^2 ∂Measure.pi fun _ => gaussianReal 0 1)≤
      (∫ x,gaussianArrayNorm (gaussianTensorJet u 0) x^2 ∂Measure.pi fun _ => gaussianReal 0 1)+
      (∫ x,gaussianArrayNorm (gaussianTensorJet u 1) x^2 ∂Measure.pi fun _ => gaussianReal 0 1) := by
  have hh := finite_divergence_l2_bound (fun j => (u j).f)
    (fun i j => ((u j).partial i).f) (fun i j k => (((u k).partial j).partial i).f)
    (fun i j => (u j).coordinate_derivative i)
    (fun i j k => ((u k).partial j).coordinate_derivative i)
    (fun i j k x => (u k).partial_commute j i x)
    (fun j => (u j).smooth.continuous.measurable) (fun j => (u j).polynomial_growth)
    (fun i j => ((u j).partial i).smooth.continuous.measurable)
    (fun i j => ((u j).partial i).polynomial_growth)
    (fun i j k => (((u k).partial j).partial i).smooth.continuous.measurable)
    (fun i j k => (((u k).partial j).partial i).polynomial_growth)
  simp only [sq_abs,gaussian_tensor_zero_square,gaussian_tensor_one_square]
  simpa only [gaussianDivergence,GaussianJet.divergence_apply] using hh

theorem gaussian_core_square_bound {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {n : ℕ} (u : Fin (n+1) → GaussianJet (n+1))
    (e : Fin (n+1) → H) (he : Orthonormal ℝ e) :
    ‖((GaussianJet.divergence u).toCylinder e).valueLp P W S hS hcore 2 (by simp)‖^2≤
      ‖gaussianTensorCore H P W S hS hcore 2 (by simp) u e 0‖^2+
      ‖gaussianTensorCore H P W S hS hcore 2 (by simp) u e 1‖^2 := by
  rw [gaussian_scalar_core_square_moment H P W S hS hcore (GaussianJet.divergence u) e he,
    gaussian_tensor_core_square_moment H P W S hS hcore u e he 0,
    gaussian_tensor_core_square_moment H P W S hS hcore u e he 1]
  exact gaussian_jet_square_bound u

end Asakura.Chapter12
