import Chapter12GaussianArrayLp
import Chapter12GaussianCoreNormTransport
import Chapter12GaussianScalarHigherCore

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)

include S hS hcore in
theorem gaussian_array_norm_transport {N : ℕ} {I K : Type*} [Fintype I] [NormedAddCommGroup K]
    (e : Fin N → H) (he : Orthonormal ℝ e) (f : I → GaussianJet N)
    (m : ℕ) (hm : 0<m) [Fact (1≤(m:ℝ≥0∞))]
    (z : Lp K (m:ℕ) P)
    (hz : (fun w => ‖z w‖)=ᵐ[P] (fun w => gaussianArrayNorm f (fun i => W (e i) w))) :
    ‖z‖=‖gaussianArrayLp f m (ENNReal.natCast_ne_top _)‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hm.ne').mp
  rw [lp_nat_norm_power m hm,lp_nat_norm_power m hm]
  calc
    _=∫ w,gaussianArrayNorm f (fun i => W (e i) w)^m ∂P :=
      integral_congr_ae (hz.fun_comp (fun a => a^m))
    _=∫ x,gaussianArrayNorm f x^m ∂Measure.pi (fun _ => gaussianReal 0 1) :=
      (wiener_orthonormal_law P W (wiener_gaussian_law_from_dense_core P W S hS hcore) e he).integral_comp
        ((gaussianArrayNorm_continuous f).pow m).aestronglyMeasurable
    _=_ := integral_congr_ae ((gaussianArrayLp_norm_coe f m (ENNReal.natCast_ne_top _)).symm.fun_comp (fun a => a^m))

theorem gaussian_vector_core_array_norm {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (e : Fin (n+1) → H) (he : Orthonormal ℝ e)
    (m : ℕ) (hm : 0<m) [Fact (1≤(m:ℝ≥0∞))] (k : ℕ) :
    ‖gaussianTensorCore H P W S hS hcore m (ENNReal.natCast_ne_top _) u e k‖=
      ‖gaussianArrayLp (gaussianDerivativeArray u k) m (ENNReal.natCast_ne_top _)‖ := by
  apply gaussian_array_norm_transport H P W S hS hcore e he (gaussianDerivativeArray u k) m hm
  simpa only [gaussian_tensor_array_norm,gaussianDerivativeNorm] using
    gaussian_tensor_core_norm H P W S hS hcore m (ENNReal.natCast_ne_top _) u e he k

end Asakura.Chapter12
