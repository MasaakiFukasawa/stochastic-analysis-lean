import Chapter9GaussianRegression
import Chapter9BoundedTests

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

noncomputable def gaussianPosteriorTest {d : ℕ} (μ : Measure (Fin d → ℝ))
    (a v : ℝ) (f : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ :=
    (∫ x,gaussianKernel a v x y*f x ∂μ)/(∫ x,gaussianKernel a v x y ∂μ)

/-- The explicit posterior expectation is bounded Borel at every observed
state; positivity of the mixture density justifies the normalization. -/
theorem gaussian_posterior_bounded_borel {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (a : ℝ) (v : ℝ≥0) (hv : v≠0) (f : (Fin d → ℝ) → ℝ) (hf : IsBoundedBorel f) :
    IsBoundedBorel (gaussianPosteriorTest μ a v f) := by
  obtain ⟨C,hC,hfC⟩ := hf.2
  have hk : Measurable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => gaussianKernel a v z.2 z.1) := by
    unfold gaussianKernel
    fun_prop
  have hm : Measurable (fun y => ∫ x,gaussianKernel a v x y*f x ∂μ) := (hk.mul (hf.1.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have hden : Measurable (fun y => ∫ x,gaussianKernel a v x y ∂μ) := hk.stronglyMeasurable.integral_prod_right'.measurable
  refine ⟨hm.div hden,C,hC,?_⟩
  intro y
  obtain ⟨hi,hp⟩ := gaussian_mixture_positive μ a v hv y
  have hb x : ‖gaussianKernel a v x y*f x‖≤C*gaussianKernel a v x y := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (gaussian_kernel_positive a v x y)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hfC x) (gaussian_kernel_positive a v x y).le
  have hh := norm_integral_le_of_norm_le (hi.const_mul C) (ae_of_all _ hb)
  rw [integral_const_mul] at hh
  change ‖(∫ x,gaussianKernel a v x y*f x ∂μ)/(∫ x,gaussianKernel a v x y ∂μ)‖≤C
  rw [norm_div,Real.norm_eq_abs (∫ x,gaussianKernel a v x y ∂μ),abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr hh

theorem gaussian_joint_bounded_regression {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (a : ℝ) (v : ℝ≥0) (hv : v≠0) (f : (Fin d → ℝ) → ℝ) (hf : IsBoundedBorel f) :
    let Q := (μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))
    Q[(fun z => f z.1)|MeasurableSpace.comap Prod.snd inferInstance]=ᵐ[Q]
      (fun z => gaussianPosteriorTest μ a v f z.2) := by
  let Q := (μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))
  haveI : IsProbabilityMeasure Q := gaussian_joint_probability μ a v hv
  have hfQ : Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => f z.1) Q :=
    (hf.comp Prod.fst measurable_fst).integrable Q
  have he := gaussian_joint_regression μ a v hv (fun z => f z.1) (hf.1.comp measurable_fst).stronglyMeasurable hfQ
  apply he.trans
  apply ae_of_all
  intro z
  dsimp only
  rw [normalized_density_integral μ (fun x => gaussianKernel a v x z.2)
    (by unfold gaussianKernel; fun_prop) (fun x => (gaussian_kernel_positive a v x z.2).le)
    _ (gaussian_mixture_positive μ a v hv z.2).2]
  simp only [gaussianPosteriorTest,smul_eq_mul,div_eq_inv_mul]
end Asakura.Chapter9
