import Chapter12RapidDecayFourierSmooth

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The Gaussian regularization of the inverse characteristic integral
has a common bound and converges pointwise as the variance decreases to zero. -/
theorem gaussian_damped_fourier_limit {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) (φ : E → ℂ) (hφ : Integrable φ ν)
    (ε : ℕ → ℝ) (hεpos : ∀ n,0≤ε n) (hε : Tendsto ε atTop (𝓝 0)) (x : E) :
    (∀ n,‖∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ*
      (Real.exp (-ε n*‖ξ‖^2/2):ℂ) ∂ν‖≤∫ ξ,‖φ ξ‖ ∂ν) ∧
    Tendsto (fun n => ∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ*
      (Real.exp (-ε n*‖ξ‖^2/2):ℂ) ∂ν) atTop
      (𝓝 (∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ ∂ν)) := by
  have hphase (ξ : E) : ‖Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))‖=1 := by
    simp [Complex.norm_exp]
  have hq (n : ℕ) (ξ : E) : Real.exp (-ε n*‖ξ‖^2/2)≤1 := by
    apply Real.exp_le_one_iff.mpr
    have hh := mul_nonneg (hεpos n) (sq_nonneg ‖ξ‖)
    linarith
  have hbound (n : ℕ) (ξ : E) : ‖Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ*
      (Real.exp (-ε n*‖ξ‖^2/2):ℂ)‖≤‖φ ξ‖ := by
    rw [norm_mul,norm_mul,hphase,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (hq n ξ)
  have hm (n : ℕ) : AEStronglyMeasurable (fun ξ => Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ*
      (Real.exp (-ε n*‖ξ‖^2/2):ℂ)) ν := by
    exact ((show Continuous (fun ξ : E => Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))) by fun_prop).aestronglyMeasurable.mul
      hφ.aestronglyMeasurable).mul (show Continuous (fun ξ : E => (Real.exp (-ε n*‖ξ‖^2/2):ℂ)) by fun_prop).aestronglyMeasurable
  constructor
  · intro n
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (ae_of_all _ (fun ξ => norm_nonneg _)) hφ.norm
        (ae_of_all _ (hbound n)))
  · apply tendsto_integral_of_dominated_convergence (fun ξ => ‖φ ξ‖) hm hφ.norm
      (fun n => ae_of_all _ (hbound n))
    apply ae_of_all
    intro ξ
    have ht : Tendsto (fun n => Real.exp (-ε n*‖ξ‖^2/2)) atTop (𝓝 1) := by
      have ht0 : Tendsto (fun n => -ε n*‖ξ‖^2/2) atTop (𝓝 0) := by
        simpa using (hε.neg.mul_const (‖ξ‖^2)).div_const 2
      simpa only [Function.comp_def, Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp ht0
    have htC := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
    simpa only [Complex.ofReal_one,mul_one] using
      (tendsto_const_nhds.mul htC : Tendsto (fun n =>
        Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ*(Real.exp (-ε n*‖ξ‖^2/2):ℂ)) atTop
        (𝓝 ((Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ)*(1:ℂ))))

end Asakura.Chapter12
