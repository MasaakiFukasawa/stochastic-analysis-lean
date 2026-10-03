import Chapter12BasketScoreDerivative
import Chapter12GammaDiagonalCorrection

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

/-- The derivative of the delta formula gives both diagonal and mixed
gamma, for a merely measurable polynomial-growth payoff. -/
theorem basket_measurable_gamma {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det≠0) (x b : Fin d → ℝ)
    (i j : Fin d) (hxi : 0<x i) (hxj : 0<x j)
    (h : (Fin d → ℝ) → ℝ) (hm : Measurable h)
    (C : ℝ) (n : ℕ) (hb : ∀ s,|h s|≤C*(1+‖s‖^n)) :
    HasDerivAt
      (fun u : ℝ => (∫ z,h (fun k => (if k=j then u else x k)*Real.exp (b k+∑ a,A k a*z a))*
        (∑ a,(A⁻¹) a i*z a) ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1))/(if i=j then u else x i))
      (∫ z,h (fun k => x k*Real.exp (b k+∑ a,A k a*z a))*
        (((∑ a,(A⁻¹) a i*z a)*(∑ a,(A⁻¹) a j*z a)-(∑ a,(A⁻¹) a i*(A⁻¹) a j)-
          (if i=j then ∑ a,(A⁻¹) a i*z a else 0))/(x i*x j))
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) (x j) := by
  classical
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  let f : (Fin d → ℝ) → ℝ := fun z => h (fun k => x k*Real.exp (b k+∑ a,A k a*z a))
  let Li : (Fin d → ℝ) → ℝ := fun z => ∑ a,(A⁻¹) a i*z a
  let Lj : (Fin d → ℝ) → ℝ := fun z => ∑ a,(A⁻¹) a j*z a
  let Q : ℝ := ∑ a,(A⁻¹) a i*(A⁻¹) a j
  have hf : MemLp f 2 μ := lognormal_polynomial_payoff_moments x b A h hm C n hb 2 (by norm_num)
  have hi : MemLp Li 4 μ := by
    simpa using (finite_gaussian_linear_score_law (fun a => (A⁻¹) a i)).memLp_comp (memLp_id_gaussianReal 4)
  have hj : MemLp Lj 4 μ := by
    simpa using (finite_gaussian_linear_score_law (fun a => (A⁻¹) a j)).memLp_comp (memLp_id_gaussianReal 4)
  have hscore : MemLp (fun z => Li z*Lj z-Q) 2 μ := (hi.mul hj).sub (memLp_const Q)
  have hJ : Integrable (fun z => f z*(Li z*Lj z-Q)) μ := hf.integrable_mul hscore
  have hI : Integrable (fun z => f z*Li z) μ := hf.integrable_mul (hi.mono_exponent (by norm_num : (2:ℝ≥0∞)≤4))
  have hd := basket_measurable_score_derivative A hA x b i j hxj h hm C n hb
  have hg := gamma_denominator_derivative i j x hxi.ne' hxj.ne' _ _ hd
  have he (k : Fin d) : (if k=j then x j else x k)=x k := by
    by_cases hk : k=j <;> simp [hk]
  simp only [he] at hg
  convert hg using 1
  by_cases hij : i=j
  · simp only [if_pos hij]
    change (∫ z,f z*((Li z*Lj z-Q-Li z)/(x i*x j)) ∂μ)=
      ((∫ z,f z*(Li z*Lj z-Q) ∂μ)-(∫ z,f z*Li z ∂μ))/(x i*x j)
    rw [← integral_sub hJ hI,← integral_div]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by dsimp only [Pi.sub_apply]; ring)
  · simp only [if_neg hij,sub_zero]
    change (∫ z,f z*((Li z*Lj z-Q)/(x i*x j)) ∂μ)=(∫ z,f z*(Li z*Lj z-Q) ∂μ)/(x i*x j)
    rw [← integral_div]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by ring)

end Asakura.Chapter12
