import Chapter12GaussianTranslationDensity
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem finite_gaussian_linear_score_law {d : ℕ} (q : Fin d → ℝ) :
    HasLaw (fun z => ∑ i,q i*z i)
      (gaussianReal 0 ⟨∑ i,(q i)^2,Finset.sum_nonneg (fun i _ => sq_nonneg _)⟩)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  let L : (Fin d → ℝ) →L[ℝ] ℝ := ∑ i,q i • ContinuousLinearMap.proj i
  have hL (z : Fin d → ℝ) : L z=∑ i,q i*z i := by
    simp [L]
  have hG : HasGaussianLaw (fun z : Fin d → ℝ => ∑ i,q i*z i) μ := by
    have he : HasLaw (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
        (stdGaussian (EuclideanSpace ℝ (Fin d))) μ := ⟨by fun_prop,map_pi_eq_stdGaussian⟩
    have hh := (he.hasGaussianLaw.map_equiv
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ))).map L
    simpa only [Function.comp_def,PiLp.continuousLinearEquiv_apply,WithLp.ofLp_toLp,hL] using hh
  have hi (i : Fin d) : MemLp (fun z : Fin d → ℝ => q i*z i) 2 μ :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i)).const_mul (q i)
  have hm : (∫ z,∑ i,q i*z i ∂μ)=0 := by
    rw [integral_finsetSum _ (fun i _ => (hi i).integrable (by simp))]
    simp only [integral_const_mul]
    have he (i : Fin d) : (∫ z : Fin d → ℝ,z i ∂μ)=0 := by
      rw [integral_eval]
      exact integral_id_gaussianReal
    simp only [he,mul_zero,Finset.sum_const_zero]
  have hv : Var[fun z : Fin d → ℝ => ∑ i,q i*z i; μ]=∑ i,(q i)^2 := by
    have he : (fun z : Fin d → ℝ => ∑ i,q i*z i)=∑ i,fun z : Fin d → ℝ => q i*z i := by
      ext z
      simp only [Finset.sum_apply]
    rw [he]
    have hh := variance_sum_pi (fun i => (memLp_id_gaussianReal (μ := 0) (v := 1) 2).const_mul (q i))
    have hvs (i : Fin d) : Var[fun x : ℝ => q i*x; gaussianReal 0 1]=(q i)^2 := by
      change Var[fun x : ℝ => q i*id x; gaussianReal 0 1]=(q i)^2
      rw [variance_const_mul,variance_id_gaussianReal]
      simp
    simpa only [hvs,id_eq] using hh
  refine ⟨hG.aemeasurable,?_⟩
  rw [hG.map_eq_gaussianReal,hm,hv]
  congr 1
  exact Real.toNNReal_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))

end Asakura.Chapter12
