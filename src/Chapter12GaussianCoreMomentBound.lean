import Chapter12GaussianCoreDivergence
import Chapter12ActualDivergenceMoment
import Chapter12MomentToSobolevNorm

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

/-- The dimension-free estimate is now on the actual cylindrical core
and its completed-Hilbert-tensor derivatives on the original probability space. -/
theorem gaussian_core_high_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {n : ℕ} (u : Fin (n+1) → GaussianJet (n+1))
    (e : Fin (n+1) → H) (he : Orthonormal ℝ e)
    (p : ℕ) (hp : 1≤p) [Fact (1≤((2*p:ℕ):ℝ≥0∞))] :
    ‖((GaussianJet.divergence u).toCylinder e).valueLp P W S hS hcore (2*p:ℕ) (by exact ENNReal.natCast_ne_top _)‖≤
      (2*(2*p-1):ℕ)*∑ k : Fin (2*p+1),
        ‖gaussianTensorCore H P W S hS hcore (2*p:ℕ) (by exact ENNReal.natCast_ne_top _) u e k‖ := by
  classical
  let Z := fun w i => W (e i) w
  have hlaw := wiener_orthonormal_law P W (wiener_gaussian_law_from_dense_core P W S hS hcore) e he
  let z := ((GaussianJet.divergence u).toCylinder e).valueLp P W S hS hcore (2*p:ℕ) (by exact ENNReal.natCast_ne_top _)
  let v := fun k : Fin (2*p+1) => gaussianTensorCore H P W S hS hcore (2*p:ℕ) (by exact ENNReal.natCast_ne_top _) u e k
  have hz : (z : Ω → ℝ)=ᵐ[P] (fun w => (GaussianJet.divergence u).f (Z w)) :=
    ((GaussianJet.divergence u).toCylinder e |>.value_memLp P W S hS hcore (2*p:ℕ) (by exact ENNReal.natCast_ne_top _)).coeFn_toLp
  have hv : ∀ k : Fin (2*p+1),(fun w => ‖v k w‖)=ᵐ[P]
      (fun w => gaussianDerivativeNorm u k (Z w)) := by
    intro k
    simpa only [gaussian_tensor_array_norm] using
      gaussian_tensor_core_norm H P W S hS hcore (2*p:ℕ) (by exact ENNReal.natCast_ne_top _) u e he k
  apply moment_to_sobolev_norm (2*p) (by omega) z v (2*(2*p-1):ℕ) (by positivity)
  have hleft : (∫ w,|z w|^(2*p) ∂P)=
      ∫ x,|(GaussianJet.divergence u).f x|^(2*p) ∂Measure.pi fun _ => gaussianReal 0 1 := by
    calc
      _=(∫ w,|(GaussianJet.divergence u).f (Z w)|^(2*p) ∂P) :=
        integral_congr_ae (hz.fun_comp (fun a => |a|^(2*p)))
      _=_ := hlaw.integral_comp (((GaussianJet.divergence u).smooth.continuous.abs.pow (2*p)).aestronglyMeasurable)
  have hright : (∫ w,(∑ k : Fin (2*p+1),‖v k w‖)^(2*p) ∂P)=
      ∫ x,gaussianSobolevSum u (2*p) x^(2*p) ∂Measure.pi fun _ => gaussianReal 0 1 := by
    calc
      _=(∫ w,gaussianSobolevSum u (2*p) (Z w)^(2*p) ∂P) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hv] with w hw
        congr 1
        exact Finset.sum_congr rfl (fun k _ => hw k)
      _=_ := by
        have hc : Continuous (gaussianSobolevSum u (2*p)) :=
          continuous_finset_sum Finset.univ (fun k _ => gaussianArrayNorm_continuous (gaussianDerivativeArray u k))
        exact hlaw.integral_comp (hc.pow (2*p)).aestronglyMeasurable
  rw [hleft,hright]
  exact actual_divergence_even_moment u p hp

end Asakura.Chapter12
