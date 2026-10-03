import Chapter6GaussianBridgeResidual

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Sum the coordinate second moments and apply the scalar second-moment
bound to the Euclidean norm. This retains the square-root dimension factor. -/
theorem gaussian_vector_norm_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (R : Ω → Fin d → ℝ)
    (hR : HasGaussianLaw R P) (v : ℝ) (hv : ∀ i,(∫ w,R w i^2 ∂P)=v) :
    MemLp (fun w => ‖WithLp.toLp 2 (R w)‖) 2 P ∧
      (∫ w,‖WithLp.toLp 2 (R w)‖ ∂P)≤Real.sqrt ((d:ℝ)*v) := by
  have hE : HasGaussianLaw (fun w => WithLp.toLp 2 (R w)) P :=
    hR.map_equiv (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hN := hE.memLp_two.norm
  have hs : (∫ w,‖WithLp.toLp 2 (R w)‖^2 ∂P)=(d:ℝ)*v := by
    simp only [EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp]
    rw [integral_finsetSum _ (fun i _ => (memLp_two_iff_integrable_sq (hR.eval i).aemeasurable.aestronglyMeasurable).mp (hR.eval i).memLp_two)]
    simp [hv]
  exact ⟨hN,by simpa only [hs] using integral_le_sqrt_second_moment P _ hN⟩

theorem gaussian_vector_square_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (R : Ω → Fin d → ℝ)
    (hR : HasGaussianLaw R P) (v : ℝ) (hv : ∀ i,(∫ w,R w i^2 ∂P)=v) :
    (∫ w,‖WithLp.toLp 2 (R w)‖^2 ∂P)=(d:ℝ)*v := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ => (memLp_two_iff_integrable_sq (hR.eval i).aemeasurable.aestronglyMeasurable).mp (hR.eval i).memLp_two)]
  simp [hv]

end Asakura.Chapter6
