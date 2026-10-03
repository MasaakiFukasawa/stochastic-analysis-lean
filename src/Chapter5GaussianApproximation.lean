import FullAuditHeatKernel

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace Asakura.Chapter5
open Asakura.FullAudit

/-- Gaussian convolution of a Lipschitz function need not have a bounded
payoff. Its at-most-linear growth is enough for integrability. -/
theorem heatAverage_integrable_lipschitz (f : ℝ → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (x t : ℝ) :
    Integrable (fun z => f (x+Real.sqrt t*z)) (gaussianReal 0 1) := by
  have hz : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num)
  have hb : Integrable (fun z : ℝ => ‖f x‖+(K:ℝ)*Real.sqrt t*‖z‖) (gaussianReal 0 1) :=
    (integrable_const _).add (hz.norm.const_mul _)
  apply hb.mono' (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  apply ae_of_all
  intro z
  have hdist := hf.dist_le_mul (x+Real.sqrt t*z) x
  rw [Real.dist_eq,Real.dist_eq,add_sub_cancel_left,abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg t)] at hdist
  calc
    ‖f (x+Real.sqrt t*z)‖ ≤ ‖f x‖+‖f (x+Real.sqrt t*z)-f x‖ := by
      simpa only [add_sub_cancel] using norm_add_le (f x) (f (x+Real.sqrt t*z)-f x)
    _ ≤ ‖f x‖+(K:ℝ)*Real.sqrt t*‖z‖ := by
      simp only [Real.norm_eq_abs]
      nlinarith only [hdist]

/-- Quantitative joint approach to t=0, with x allowed to vary.
This supplies the endpoint limit needed by the representation argument. -/
theorem heatAverage_endpoint_bound (f : ℝ → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (x y t : ℝ) :
    |heatAverage f x t-f y| ≤
      (K:ℝ)*(|x-y|+Real.sqrt t*(∫ z : ℝ, |z| ∂gaussianReal 0 1)) := by
  have hz : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num)
  have hi := heatAverage_integrable_lipschitz f K hf x t
  have he : heatAverage f x t-f y = ∫ z, f (x+Real.sqrt t*z)-f y ∂gaussianReal 0 1 := by
    rw [integral_sub hi (integrable_const _)];simp [heatAverage]
  rw [he]
  calc
    _ ≤ ∫ z, |f (x+Real.sqrt t*z)-f y| ∂gaussianReal 0 1 :=
      by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z : ℝ => f (x+Real.sqrt t*z)-f y) (μ := gaussianReal 0 1)
    _ ≤ ∫ z : ℝ, (K:ℝ)*(|x-y|+Real.sqrt t*|z|) ∂gaussianReal 0 1 := by
      apply integral_mono (hi.sub (integrable_const _)).norm
        (((integrable_const _).add (hz.norm.const_mul _)).const_mul _)
      intro z
      have h := hf.dist_le_mul (x+Real.sqrt t*z) y
      simp only [Real.dist_eq] at h
      apply h.trans
      apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
      have he' : x+Real.sqrt t*z-y = (x-y)+Real.sqrt t*z := by ring
      rw [he']
      simpa [abs_mul,abs_of_nonneg (Real.sqrt_nonneg t)] using abs_add_le (x-y) (Real.sqrt t*z)
    _ = _ := by
      have hza : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by simpa only [Real.norm_eq_abs] using hz.norm
      rw [integral_const_mul,integral_add (integrable_const _) (hza.const_mul _),integral_const_mul]
      simp

end Asakura.Chapter5
