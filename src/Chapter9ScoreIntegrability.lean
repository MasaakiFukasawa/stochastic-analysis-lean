import Chapter9GaussianRegression
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace Asakura.Chapter9
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

noncomputable def componentScore {d : ℕ} (a v : ℝ)
    (z : (Fin d → ℝ) × (Fin d → ℝ)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => -(z.2 i-a*z.1 i)/v)

theorem gaussian_component_score_memLp {d : ℕ} (a : ℝ) (v : ℝ≥0) (x : Fin d → ℝ) :
    MemLp (fun y => componentScore a v (x,y)) 2
      (Measure.pi (fun i => gaussianReal (a*x i) v)) := by
  apply MemLp.of_eval_piLp
  intro i
  have hi : MemLp (fun y : Fin d → ℝ => y i) 2
      (Measure.pi (fun i => gaussianReal (a*x i) v)) := by
    simpa only [Function.comp_def,Function.eval,id_eq] using
      (IsGaussian.memLp_two_id (μ := gaussianReal (a*x i) v)).comp_measurePreserving
        (measurePreserving_eval (fun i => gaussianReal (a*x i) v) i)
  simpa only [componentScore,WithLp.ofLp_toLp,Pi.neg_apply,Pi.sub_apply,
    div_eq_mul_inv,mul_comm] using
    (hi.sub (memLp_const (a*x i))).neg.const_mul ((v:ℝ)⁻¹)

theorem gaussian_component_score_moment {d : ℕ} (a : ℝ) (v : ℝ≥0) (hv : v≠0)
    (x : Fin d → ℝ) :
    (∫ y,‖componentScore a v (x,y)‖^2 ∂Measure.pi (fun i => gaussianReal (a*x i) v))=
      (d:ℝ)/v := by
  have hM := gaussian_component_score_memLp a v x
  have hii i : Integrable (fun y => (-(y i-a*x i)/(v:ℝ))^2)
      (Measure.pi (fun i => gaussianReal (a*x i) v)) :=
    (memLp_two_iff_integrable_sq (hM.eval_piLp i).aestronglyMeasurable).mp (hM.eval_piLp i)
  have hm i : (∫ y,(y i-a*x i)^2 ∂Measure.pi (fun i => gaussianReal (a*x i) v))=(v:ℝ) := by
    rw [integral_comp_eval (μ := fun i => gaussianReal (a*x i) v) (i := i)
      (f := fun y : ℝ => (y-a*x i)^2) (by fun_prop)]
    have hh := variance_eq_integral (μ := gaussianReal (a*x i) v) (X := id) measurable_id.aemeasurable
    simpa using hh.symm
  simp only [componentScore,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp]
  rw [integral_finsetSum _ (fun i _ => hii i)]
  simp_rw [div_pow,neg_sq,integral_div,hm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hv' : (v:ℝ)≠0 := by exact_mod_cast hv
  field_simp

/-- Every fiber has the same finite weighted score energy, d/v. -/
theorem gaussian_weighted_score_moment {d : ℕ} (a : ℝ) (v : ℝ≥0) (hv : v≠0)
    (x : Fin d → ℝ) :
    Integrable (fun y => gaussianKernel a v x y*‖componentScore a v (x,y)‖^2) ∧
    (∫ y,gaussianKernel a v x y*‖componentScore a v (x,y)‖^2)=(d:ℝ)/v := by
  have hm : Measurable (fun y => gaussianKernel a v x y) := by unfold gaussianKernel; fun_prop
  have hpos y : 0≤gaussianKernel a v x y := (gaussian_kernel_positive a v x y).le
  have hM := gaussian_component_score_memLp a v x
  have hi := (memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable).mp hM
  rw [gaussian_kernel_density a v hv x] at hi
  have hi' := (integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hi
  refine ⟨?_,?_⟩
  · simpa only [ENNReal.toReal_ofReal (hpos _),smul_eq_mul] using hi'
  · have hh := gaussian_component_score_moment a v hv x
    rw [gaussian_kernel_density a v hv x,
      integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))] at hh
    simpa only [ENNReal.toReal_ofReal (hpos _),smul_eq_mul] using hh

/-- The actual regression target is in L² of the constructed joint law.
The initial distribution needs no density and no moment assumption. -/
theorem gaussian_joint_score_memLp {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (a : ℝ) (v : ℝ≥0) (hv : v≠0) :
    MemLp (componentScore (d := d) a v) 2
      ((μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))) := by
  let F := fun z : (Fin d → ℝ) × (Fin d → ℝ) =>
    gaussianKernel a v z.1 z.2*‖componentScore a v z‖^2
  have hm : Measurable F := by unfold F componentScore gaussianKernel; fun_prop
  have hp z : 0≤F z := mul_nonneg (gaussian_kernel_positive a v z.1 z.2).le (sq_nonneg _)
  have hinner x : (∫ y,‖F (x,y)‖)=(d:ℝ)/v := by
    simp only [Real.norm_eq_abs,abs_of_nonneg (hp _)]
    exact (gaussian_weighted_score_moment a v hv x).2
  have hi : Integrable F (μ.prod volume) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ (fun x => (gaussian_weighted_score_moment a v hv x).1)
    · simp only [hinner]
      exact integrable_const _
  have hSc : Continuous (componentScore (d := d) a v) := by
    unfold componentScore
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hSc.aestronglyMeasurable).mpr
  have hk : Measurable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => gaussianKernel a v z.1 z.2) := by
    unfold gaussianKernel
    fun_prop
  apply (integrable_withDensity_iff_integrable_smul' hk.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (gaussian_kernel_positive a v _ _).le,smul_eq_mul] using hi
end Asakura.Chapter9
