import Chapter12HilbertOutputCoreGraph
import Chapter12HilbertMomentNorm

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

/-- A finite smooth field with values in H tensor K has a dimension-free
estimate in the actual Lp spaces of completed Hilbert tensors. -/
theorem hilbert_output_core_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (H K : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {n k : ℕ} (u : Fin k → Fin (n+1) → GaussianJet (n+1))
    (e : Fin (n+1) → H) (v : Fin k → K) (he : Orthonormal ℝ e) (hv : Orthonormal ℝ v)
    (p : ℕ) (hp : 0<p) [Fact (1≤((2*p:ℕ):ℝ≥0∞))] :
    ‖∑ a,vectorCylinderValue P W S hS hcore ((GaussianJet.divergence (u a)).toCylinder e)
      (v a) (2*p:ℕ) (ENNReal.natCast_ne_top _)‖ ≤
    (2*(2*p-1):ℕ)*∑ j : Fin (2*p+1),
      ‖gaussianHilbertOutputCore H K P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _) u e v j‖ := by
  classical
  let Z := fun w i => W (e i) w
  let z : Lp K (2*p:ℕ) P := ∑ a,vectorCylinderValue P W S hS hcore
    ((GaussianJet.divergence (u a)).toCylinder e) (v a) (2*p:ℕ) (ENNReal.natCast_ne_top _)
  let V := fun j : Fin (2*p+1) => gaussianHilbertOutputCore H K P W S hS hcore
    (2*p:ℕ) (ENNReal.natCast_ne_top _) u e v j
  have hlaw := wiener_orthonormal_law P W (wiener_gaussian_law_from_dense_core P W S hS hcore) e he
  have hz : (fun w => ‖z w‖)=ᵐ[P]
      (fun w => gaussianArrayNorm (fun a => GaussianJet.divergence (u a)) (Z w)) := by
    have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun a => vectorCylinderValue P W S hS hcore
      ((GaussianJet.divergence (u a)).toCylinder e) (v a) (2*p:ℕ) (ENNReal.natCast_ne_top _))
    have ht := ae_all_iff.mpr (fun a => vector_cylinder_value_coe H P W S hS hcore
      (2*p:ℕ) (ENNReal.natCast_ne_top _) ((GaussianJet.divergence (u a)).toCylinder e) (v a))
    filter_upwards [hs,ht] with w hsw htw
    change ‖(∑ a,vectorCylinderValue P W S hS hcore ((GaussianJet.divergence (u a)).toCylinder e)
      (v a) (2*p:ℕ) (ENNReal.natCast_ne_top _)) w‖=_
    rw [hsw]
    simp_rw [htw]
    exact orthonormal_sum_norm v hv _
  have hV : ∀ j : Fin (2*p+1),(fun w => ‖V j w‖)=ᵐ[P]
      (fun w => gaussianVectorDerivativeNorm u j (Z w)) := fun j =>
    gaussian_hilbert_output_core_norm H K P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _) u e v he hv j
  apply hilbert_moment_to_sobolev_norm (2*p) (by omega) z V (2*(2*p-1):ℕ) (by positivity)
  have hleft : (∫ w,‖z w‖^(2*p) ∂P)=
      ∫ x,gaussianArrayNorm (fun a => GaussianJet.divergence (u a)) x^(2*p)
        ∂Measure.pi (fun _ => gaussianReal 0 1) := by
    calc
      _=∫ w,gaussianArrayNorm (fun a => GaussianJet.divergence (u a)) (Z w)^(2*p) ∂P :=
        integral_congr_ae (hz.fun_comp (fun x => x^(2*p)))
      _=_ := hlaw.integral_comp ((gaussianArrayNorm_continuous _).pow (2*p)).aestronglyMeasurable
  have hright : (∫ w,(∑ j : Fin (2*p+1),‖V j w‖)^(2*p) ∂P)=
      ∫ x,gaussianVectorSobolevSum u (2*p) x^(2*p) ∂Measure.pi (fun _ => gaussianReal 0 1) := by
    calc
      _=∫ w,gaussianVectorSobolevSum u (2*p) (Z w)^(2*p) ∂P := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hV] with w hw
        congr 1
        exact Finset.sum_congr rfl (fun j _ => hw j)
      _=_ := by
        have hc : Continuous (gaussianVectorSobolevSum u (2*p)) :=
          continuous_finset_sum _ (fun j _ => gaussianArrayNorm_continuous _)
        exact hlaw.integral_comp (hc.pow (2*p)).aestronglyMeasurable
  rw [hleft,hright]
  exact actual_vector_divergence_even_moment u p hp

end Asakura.Chapter12
