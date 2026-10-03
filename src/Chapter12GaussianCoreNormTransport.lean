import Chapter12GaussianCoreMomentBound

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)

theorem gaussian_tensor_core_moment {N : ℕ} (u : Fin N → GaussianJet N)
    (e : Fin N → H) (he : Orthonormal ℝ e)
    (m : ℕ) (hm : 0<m) [Fact (1≤(m:ℝ≥0∞))] (k : ℕ) :
    ‖gaussianTensorCore H P W S hS hcore m (ENNReal.natCast_ne_top _) u e k‖^m=
      ∫ x,gaussianArrayNorm (gaussianTensorJet u k) x^m ∂Measure.pi fun _ => gaussianReal 0 1 := by
  rw [lp_nat_norm_power m hm]
  have h := gaussian_tensor_core_norm H P W S hS hcore m (ENNReal.natCast_ne_top _) u e he k
  calc
    _=(∫ w,gaussianArrayNorm (gaussianTensorJet u k) (fun i => W (e i) w)^m ∂P) :=
      integral_congr_ae (h.fun_comp (fun a => a^m))
    _=_ := (wiener_orthonormal_law P W
      (wiener_gaussian_law_from_dense_core P W S hS hcore) e he).integral_comp
        ((gaussianArrayNorm_continuous _).pow m).aestronglyMeasurable

theorem gaussian_scalar_core_moment {N : ℕ} (f : GaussianJet N)
    (e : Fin N → H) (he : Orthonormal ℝ e)
    (m : ℕ) (hm : 0<m) [Fact (1≤(m:ℝ≥0∞))] :
    ‖(f.toCylinder e).valueLp P W S hS hcore m (ENNReal.natCast_ne_top _)‖^m=
      ∫ x,|f.f x|^m ∂Measure.pi fun _ => gaussianReal 0 1 := by
  rw [lp_nat_norm_power m hm]
  have h := (f.toCylinder e |>.value_memLp P W S hS hcore m (ENNReal.natCast_ne_top _)).coeFn_toLp
  calc
    _=(∫ w,|f.f (fun i => W (e i) w)|^m ∂P) := by
      apply integral_congr_ae
      filter_upwards [h] with w hw
      change (f.toCylinder e).valueLp P W S hS hcore m (ENNReal.natCast_ne_top _) w=_ at hw
      rw [hw]
      rfl
    _=_ := (wiener_orthonormal_law P W
      (wiener_gaussian_law_from_dense_core P W S hS hcore) e he).integral_comp
        (f.smooth.continuous.abs.pow m).aestronglyMeasurable

end Asakura.Chapter12
