import Chapter12GaussianProjectionMoment

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem gaussian_even_moment_integrable (p : ℕ) :
    Integrable (fun x : ℝ => x^(2*p)) (gaussianReal 0 1) := by
  have hi := (memLp_id_gaussianReal' (μ:=0) (v:=1) (2*p:ℕ) (ENNReal.natCast_ne_top _)).integrable_norm_pow'
  convert hi using 1
  funext x
  change x^(2*p)=‖x‖^(2*p)
  rw [Real.norm_eq_abs,←abs_pow,abs_of_nonneg]
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg x) p

theorem gaussian_even_moment_pos (p : ℕ) : 0<gaussianEvenMoment p := by
  have hnon (x : ℝ) : 0≤x^(2*p) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) p
  have hn : 0≤gaussianEvenMoment p := integral_nonneg hnon
  by_contra h
  have hz : gaussianEvenMoment p=0 := le_antisymm (le_of_not_gt h) hn
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hnon)
    (gaussian_even_moment_integrable p)).mp hz
  letI := nullSingletonClass_gaussianReal (μ:=0) (v:=1) (by norm_num)
  have hne : ∀ᵐ x : ℝ ∂gaussianReal 0 1,x≠0 := by
    rw [ae_iff]
    simpa using (measure_singleton (μ:=gaussianReal 0 1) (0:ℝ))
  obtain ⟨x,hx,hzero⟩ := (hne.and hae).exists
  exact (pow_ne_zero (2*p) hx) hzero

end Asakura.Chapter12
