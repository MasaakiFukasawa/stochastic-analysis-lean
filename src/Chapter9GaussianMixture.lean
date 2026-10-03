import Chapter9KernelDensity
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal BigOperators
namespace Asakura.Chapter9
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Pointwise Gaussian kernels are uniformly bounded in the initial state;
no moment or density assumption on the initial distribution is needed. -/
theorem gaussian_kernel_bound {d : ℕ} (a : ℝ) (v : ℝ≥0) (hv : v≠0)
    (x y : Fin d → ℝ) :
    ‖gaussianKernel a v x y‖≤Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*(v:ℝ))) := by
  rw [Real.norm_eq_abs,abs_of_pos (gaussian_kernel_positive _ _ _ _)]
  apply Real.exp_le_exp.mpr
  apply sub_le_self
  exact div_nonneg (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)

theorem gaussian_mixture_positive {d : ℕ} (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] (a : ℝ) (v : ℝ≥0) (hv : v≠0) (y : Fin d → ℝ) :
    Integrable (fun x => gaussianKernel a v x y) μ ∧
      0<∫ x,gaussianKernel a v x y ∂μ := by
  have hm : Measurable (fun x => gaussianKernel a v x y) := by unfold gaussianKernel; fun_prop
  have hi : Integrable (fun x => gaussianKernel a v x y) μ :=
    (integrable_const _).mono' hm.aestronglyMeasurable (ae_of_all _ (fun x => gaussian_kernel_bound a v hv x y))
  refine ⟨hi,?_⟩
  apply (integral_pos_iff_support_of_nonneg (fun x => (gaussian_kernel_positive a v x y).le) hi).mpr
  have hs : Function.support (fun x => gaussianKernel a v x y)=univ := by
    ext x
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (gaussian_kernel_positive a v x y).ne'
  rw [hs,measure_univ]
  exact zero_lt_one

/-- The marginal density follows by Tonelli, for any initial probability
measure, including a discrete one. -/
theorem product_density_snd {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (k : A × B → ℝ≥0∞) (hk : Measurable k) :
    ((μ.prod ν).withDensity k).map Prod.snd=
      ν.withDensity (fun y => ∫⁻ x,k (x,y) ∂μ) := by
  ext S hS
  rw [Measure.map_apply measurable_snd hS,withDensity_apply _ (measurable_snd hS),withDensity_apply _ hS]
  have hs : (Prod.snd : A × B → B) ⁻¹' S=univ ×ˢ S := by ext z; simp
  rw [hs,←Measure.prod_restrict,Measure.restrict_univ]
  exact lintegral_prod_symm k hk.aemeasurable

theorem gaussian_mixture_marginal {d : ℕ} (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] (a : ℝ) (v : ℝ≥0) (hv : v≠0) :
    ((μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))).map Prod.snd=
      (volume : Measure (Fin d → ℝ)).withDensity
        (fun y => ENNReal.ofReal (∫ x,gaussianKernel a v x y ∂μ)) := by
  have hm : Measurable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => gaussianKernel a v z.1 z.2) := by
    unfold gaussianKernel
    fun_prop
  rw [product_density_snd μ volume _ hm.ennreal_ofReal]
  congr 1
  funext y
  exact (ofReal_integral_eq_lintegral_ofReal (gaussian_mixture_positive μ a v hv y).1
    (ae_of_all _ (fun x => (gaussian_kernel_positive a v x y).le))).symm
end Asakura.Chapter9
