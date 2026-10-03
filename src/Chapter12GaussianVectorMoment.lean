import Chapter12GaussianProjectionSobolev
import Chapter12ProjectionAveraging
import Chapter12ActualDivergenceMoment

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem GaussianJet.even_power_integrable {n : ℕ} (f : GaussianJet n) (p : ℕ) :
    Integrable (fun x => f.f x^(2*p)) (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hi := (f.all_moments (2*p:ℕ) (ENNReal.natCast_ne_top _)).integrable_norm_pow'
  simpa only [Real.norm_eq_abs,(even_two_mul p).pow_abs] using hi

theorem projected_divergence_value {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (z : Fin k → ℝ) (x : Fin (n+1) → ℝ) :
    (GaussianJet.divergence (projectedGaussianField u z)).f x=
      ∑ a,(GaussianJet.divergence (u a)).f x*z a := by
  change (GaussianJet.divergence (fun i => gaussianJetProjection (fun a => u a i) z)).f x=_
  rw [gaussianJetProjection_divergence,gaussianJetProjection_apply]
  exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

/-- The finite Hilbert-valued divergence estimate, with no factor involving
either the Gaussian coordinate dimension or the output dimension. -/
theorem actual_vector_divergence_even_moment {n k : ℕ}
    (u : Fin k → Fin (n+1) → GaussianJet (n+1)) (p : ℕ) (hp : 0<p) :
    (∫ x,gaussianArrayNorm (fun a => GaussianJet.divergence (u a)) x^(2*p)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
    (2*(2*p-1):ℕ)^(2*p) *
      (∫ x,gaussianVectorSobolevSum u (2*p) x^(2*p)
        ∂Measure.pi (fun _ => gaussianReal 0 1)) := by
  let P := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  let Q := Measure.pi (fun _ : Fin k => gaussianReal 0 1)
  let A := fun z x => (GaussianJet.divergence (projectedGaussianField u z)).f x^(2*p)
  let B := fun z x => gaussianSobolevSum (projectedGaussianField u z) (2*p) x^(2*p)
  let C := fun x => gaussianArrayNorm (fun a => GaussianJet.divergence (u a)) x^(2*p)
  let D := fun x => gaussianVectorSobolevSum u (2*p) x^(2*p)
  have hAm : Measurable (Function.uncurry A) := by
    change Measurable (fun z : (Fin k → ℝ) × (Fin (n+1) → ℝ) =>
      (GaussianJet.divergence (projectedGaussianField u z.1)).f z.2^(2*p))
    simp only [projected_divergence_value]
    apply Continuous.measurable
    apply Continuous.pow
    exact continuous_finset_sum _ (fun a _ =>
      ((GaussianJet.divergence (u a)).smooth.continuous.comp continuous_snd).mul
        ((continuous_apply a).comp continuous_fst))
  have hBm : Measurable (Function.uncurry B) :=
    ((gaussian_projection_sobolev_joint_continuous u (2*p)).pow (2*p)).measurable
  apply projection_averaging_bound P Q A B C D hAm hBm
    (fun z x => (even_two_mul p).pow_nonneg _) (fun z x => pow_nonneg (gaussianSobolevSum_nonneg _ _ _) _)
    (fun x => pow_nonneg (Real.sqrt_nonneg _) _) (fun x => pow_nonneg (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) _)
    (fun z => (GaussianJet.divergence (projectedGaussianField u z)).even_power_integrable p)
    (fun z => gaussianSobolevSum_power_integrable (projectedGaussianField u z) (2*p) (2*p))
    (fun x => ?_) (fun x => gaussian_projection_sobolev_integrable u (2*p) (2*p) x)
    (gaussian_array_norm_power_integrable _ (2*p))
    (gaussian_sum_array_norm_power_integrable (fun j : Fin (2*p+1) =>
      fun ab : Fin k × (Fin (j.val+1) → Fin (n+1)) => gaussianDerivativeArray (u ab.1) j ab.2) (2*p))
    (gaussianEvenMoment p) ((2*(2*p-1):ℕ)^(2*p)) (gaussian_even_moment_pos p) (by positivity)
    (fun x => ?_) (fun x => gaussian_projection_sobolev_moment u (2*p) p hp x) (fun z => ?_)
  · change Integrable (fun z => (GaussianJet.divergence (projectedGaussianField u z)).f x^(2*p)) Q
    simp only [projected_divergence_value]
    exact (gaussianLinearFormJet (fun a => (GaussianJet.divergence (u a)).f x)).even_power_integrable p
  · change (∫ z,(GaussianJet.divergence (projectedGaussianField u z)).f x^(2*p) ∂Q)=_
    simp only [projected_divergence_value]
    exact gaussian_projection_even_moment (fun a => (GaussianJet.divergence (u a)).f x) p
  · exact (le_abs_self _).trans (actual_divergence_moment_bound (projectedGaussianField u z) (2*p) (by omega))

end Asakura.Chapter12
