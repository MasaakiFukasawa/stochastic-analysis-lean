import Chapter12GaussianDampedFourierLimit

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The same domination controls the Fourier error independently of the
spatial point, giving the uniform convergence stated in the manuscript. -/
theorem uniform_fourier_damping_limit {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) (φ : E → ℂ) (hφ : Integrable φ ν)
    (q : ℕ → E → ℂ) (hq : ∀ n,AEStronglyMeasurable (q n) ν)
    (hb : ∀ n ξ,‖q n ξ‖≤1)
    (hl : ∀ ξ,Tendsto (fun n => q n ξ) atTop (𝓝 1)) :
    TendstoUniformly (fun n x => ∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ*q n ξ ∂ν)
      (fun x => ∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ ∂ν) atTop := by
  have herr (n ξ) : ‖q n ξ-1‖≤2 := by
    calc
      ‖q n ξ-1‖≤‖q n ξ‖+‖(1:ℂ)‖ := norm_sub_le _ _
      _≤2 := by simpa only [norm_one] using (show ‖q n ξ‖+1≤2 by linarith [hb n ξ])
  have hi (n) : Integrable (fun ξ => ‖φ ξ‖*‖q n ξ-1‖) ν := by
    apply (hφ.norm.mul_const 2).mono' (hφ.aestronglyMeasurable.norm.mul
      ((hq n).sub aestronglyMeasurable_const).norm)
    apply ae_of_all
    intro ξ
    change ‖‖φ ξ‖*‖q n ξ-1‖‖≤‖φ ξ‖*2
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (herr n ξ) (norm_nonneg _)
  have ht : Tendsto (fun n => ∫ ξ,‖φ ξ‖*‖q n ξ-1‖ ∂ν) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (fun ξ => ‖φ ξ‖*2)
      (fun n => hφ.aestronglyMeasurable.norm.mul ((hq n).sub aestronglyMeasurable_const).norm)
      (hφ.norm.mul_const 2)
      (fun n => ae_of_all _ (fun ξ => by
        change ‖‖φ ξ‖*‖q n ξ-1‖‖≤‖φ ξ‖*2
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_left (herr n ξ) (norm_nonneg _)))
      (ae_of_all _ (fun ξ => by
        have hs := ((hl ξ).sub_const 1).norm.const_mul ‖φ ξ‖
        simpa using hs))
    simpa using hh
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [ht.eventually (eventually_lt_nhds hε)] with n hn
  intro x
  have phase (ξ) : ‖Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))‖=1 := by simp [Complex.norm_exp]
  have hbase : Integrable (fun ξ => Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ) ν := by
    apply hφ.norm.mono' ((show Continuous (fun ξ : E =>
      Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))) by fun_prop).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
    exact ae_of_all _ (fun ξ => by
      change ‖Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ‖≤‖φ ξ‖
      rw [norm_mul,phase,one_mul])
  have hdamp : Integrable (fun ξ => Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ*q n ξ) ν := by
    apply hφ.norm.mono' (hbase.aestronglyMeasurable.mul (hq n))
    exact ae_of_all _ (fun ξ => by
      change ‖Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ*q n ξ‖≤‖φ ξ‖
      rw [norm_mul,norm_mul,phase,one_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hb n ξ))
  rw [dist_eq_norm,← integral_sub hbase hdamp]
  apply lt_of_le_of_lt (norm_integral_le_integral_norm _) ?_
  have he (ξ) : ‖Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ-
      Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ*q n ξ‖=‖φ ξ‖*‖q n ξ-1‖ := by
    rw [← mul_one_sub,norm_mul,norm_mul,phase,one_mul,norm_sub_rev]
  simpa only [he] using hn

end Asakura.Chapter12
