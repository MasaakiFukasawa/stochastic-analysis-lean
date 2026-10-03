import Chapter9CouplingMoments
import Chapter8VectorOUConvergence

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem standard_gaussian_second_moment (d : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin d),‖x‖^2 ∂stdGaussian (EuclideanSpace ℝ (Fin d)))=d := by
  have hreal : (∫ x : ℝ,x^2 ∂gaussianReal 0 1)=1 := by
    have hv := variance_eq_sub (μ := gaussianReal 0 1) (X := id) IsGaussian.memLp_two_id
    simpa using hv.symm
  have hi : Integrable (fun x : ℝ => x^2) (gaussianReal 0 1) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mp IsGaussian.memLp_two_id
  rw [←map_pi_eq_stdGaussian,integral_map (by fun_prop) (by fun_prop)]
  simp only [EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp]
  have hii (i : Fin d) : Integrable (fun x : Fin d → ℝ => (x i)^2)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) :=
    by
      simpa only [Function.comp_def,Function.eval] using
        (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i).integrable_comp_of_integrable hi
  rw [integral_finsetSum _ (fun i _ => hii i)]
  have he (i : Fin d) :
      (∫ x : Fin d → ℝ,(x i)^2 ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1))=1 := by
    rw [integral_comp_eval (μ := fun _ : Fin d => gaussianReal 0 1) (i := i) (f := fun x : ℝ => x^2) (by fun_prop)]
    exact hreal
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

theorem gaussian_affine_second_moment {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x => x) 2 μ) (a b : ℝ) :
    (∫ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ‖a • z.1+b • z.2‖^2 ∂μ.prod (stdGaussian (EuclideanSpace ℝ (Fin d))))=
      a^2*(∫ x,‖x‖^2 ∂μ)+b^2*d := by
  rw [independent_affine_second_moment μ _ hμ IsGaussian.memLp_two_id
    integral_id_stdGaussian a b,standard_gaussian_second_moment]

theorem distance_to_standard_gaussian {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x => x) 2 μ) :
    Asakura.FullAudit.transportDistance μ (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      Real.sqrt ((∫ x,‖x‖^2 ∂μ)+(d:ℝ)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hγ : MemLp (fun x => x) 2 γ := IsGaussian.memLp_two_id
  have hx : MemLp (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => z.1) 2 (μ.prod γ) :=
    hμ.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := γ))
  have hy : MemLp (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => z.2) 2 (μ.prod γ) :=
    hγ.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := γ))
  have hi := (memLp_two_iff_integrable_sq_norm (hx.sub hy).aestronglyMeasurable).mp (hx.sub hy)
  have hb := transport_distance_sq_le_displacement (μ.prod γ) Prod.fst Prod.snd
    measurable_fst measurable_snd hi
  rw [(measurePreserving_fst (μ := μ) (ν := γ)).map_eq,
    (measurePreserving_snd (μ := μ) (ν := γ)).map_eq] at hb
  have hm := gaussian_affine_second_moment μ hμ 1 (-1)
  simp only [one_smul,neg_one_smul,one_pow,neg_one_sq,one_mul,←sub_eq_add_neg] at hm
  rw [hm] at hb
  exact le_trans (le_abs_self _) (by
    rw [←Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hb)
end Asakura.Chapter9
