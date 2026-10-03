import Chapter12GaussianCoreMomentBound

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

theorem lp_two_norm_square {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {P : Measure Ω} (f : Lp E 2 P) :
    ‖f‖^2=∫ x,‖f x‖^2 ∂P := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)

theorem gaussian_tensor_core_square_moment {N : ℕ} (u : Fin N → GaussianJet N)
    (e : Fin N → H) (he : Orthonormal ℝ e)
    (k : ℕ) :
    ‖gaussianTensorCore H P W S hS hcore 2 (by simp) u e k‖^2=
      ∫ x,gaussianArrayNorm (gaussianTensorJet u k) x^2 ∂Measure.pi fun _ => gaussianReal 0 1 := by
  rw [lp_two_norm_square]
  have h := gaussian_tensor_core_norm H P W S hS hcore 2 (by simp) u e he k
  calc
    _=(∫ w,gaussianArrayNorm (gaussianTensorJet u k) (fun i => W (e i) w)^2 ∂P) :=
      integral_congr_ae (h.fun_comp (fun a => a^2))
    _=_ := (wiener_orthonormal_law P W
      (wiener_gaussian_law_from_dense_core P W S hS hcore) e he).integral_comp
        ((gaussianArrayNorm_continuous _).pow 2).aestronglyMeasurable

theorem gaussian_scalar_core_square_moment {N : ℕ} (f : GaussianJet N)
    (e : Fin N → H) (he : Orthonormal ℝ e)
    :
    ‖(f.toCylinder e).valueLp P W S hS hcore 2 (by simp)‖^2=
      ∫ x,|f.f x|^2 ∂Measure.pi fun _ => gaussianReal 0 1 := by
  rw [lp_two_norm_square]
  have h := (f.toCylinder e |>.value_memLp P W S hS hcore 2 (by simp)).coeFn_toLp
  calc
    _=(∫ w,|f.f (fun i => W (e i) w)|^2 ∂P) := by
      apply integral_congr_ae
      filter_upwards [h] with w hw
      change (f.toCylinder e).valueLp P W S hS hcore 2 (by simp) w=_ at hw
      rw [hw]
      rfl
    _=_ := (wiener_orthonormal_law P W
      (wiener_gaussian_law_from_dense_core P W S hS hcore) e he).integral_comp
        (f.smooth.continuous.abs.pow 2).aestronglyMeasurable

end Asakura.Chapter12
