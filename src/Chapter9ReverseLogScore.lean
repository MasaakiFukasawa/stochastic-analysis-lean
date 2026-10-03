import Chapter9ReverseFields
import Chapter9ActualForwardPDE

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The actual drift field is x+2∇log p, not merely a formal score symbol. -/
theorem ou_reverse_drift_log_score {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0<t) (x : Fin d → ℝ) (i : Fin d) :
    ouReverseDrift μ (t,x) i=x i+
      2*directional (fun y => Real.log (ouCoordinateDensity μ (t,y))) (Pi.single i 1) x := by
  have hp : ContDiff ℝ ∞ (fun y => ouCoordinateDensity μ (t,y)) := ou_mixture_slice_smooth μ t ht
  have hpos := ou_coordinate_density_positive μ t ht x
  have hsm : ContDiffAt ℝ ∞ (ouCoordinateDensity μ) (t,x) :=
    (ou_gaussian_mixture_smooth μ).contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)
  have hj : fderiv ℝ (ouCoordinateDensity μ) (t,x) ((0:ℝ),Pi.single i 1)=
      directional (fun y => ouCoordinateDensity μ (t,y)) (Pi.single i 1) x := by
    simpa only [iteratedFDeriv_one_apply] using spatial_slice_first_jet (ouCoordinateDensity μ) t x (Pi.single i 1) hsm
  have hlog : directional (fun y => Real.log (ouCoordinateDensity μ (t,y))) (Pi.single i 1) x=
      directional (fun y => ouCoordinateDensity μ (t,y)) (Pi.single i 1) x/ouCoordinateDensity μ (t,x) := by
    unfold directional
    rw [fderiv.log (hp.differentiable (by simp) x) hpos.ne']
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,div_eq_mul_inv]
    ring
  dsimp only [ouReverseDrift]
  rw [hj,hlog]
  ring
end Asakura.Chapter9
