import EndToEndJointGaussianMartingale
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace Asakura.EndToEnd
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ι × ℝ≥0 → Ω → ℝ)
    (hZ : IsGaussianProcess Z P) (hm : ∀ q, Measurable (Z q))
    (hmean : ∀ q, ∫ ω, Z q ω ∂P = 0)
    (hcov : ∀ i j u v, cov[Z (i,u), Z (j,v); P] =
      if i = j then ((min u v : ℝ≥0) : ℝ) else 0)

include hZ hmean hcov in
theorem joint_increment_product_mean (i j : ι) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, (Z (i,t) ω-Z (i,s) ω)*(Z (j,t) ω-Z (j,s) ω) ∂P) =
      if i=j then (t:ℝ)-(s:ℝ) else 0 := by
  have hi q := (hZ.hasGaussianLaw_eval q).memLp_two
  have h := covariance_fun_sub_fun_sub (hi (i,t)) (hi (i,s)) (hi (j,t)) (hi (j,s))
  have hc := covariance_eq_sub ((hi (i,t)).sub (hi (i,s))) ((hi (j,t)).sub (hi (j,s)))
  simp only [Pi.sub_def, Pi.mul_def] at hc
  rw [hc,
    gaussian_joint_increment_mean P Z hZ hmean,
    gaussian_joint_increment_mean P Z hZ hmean, mul_zero, sub_zero] at h
  rw [hcov,hcov,hcov,hcov] at h
  by_cases hij : i=j <;> simpa [hij,min_eq_right hst,min_eq_left hst] using h

include hZ hm hmean hcov in
theorem gaussian_joint_product_martingale (i j : ι) (s t : ℝ≥0) (hst : s ≤ t) :
    P[(fun ω => Z (i,t) ω*Z (j,t) ω-(if i=j then (t:ℝ) else 0)) | jointPast Z s] =ᵐ[P]
      fun ω => Z (i,s) ω*Z (j,s) ω-(if i=j then (s:ℝ) else 0) := by
  let D (k : ι) := fun ω => Z (k,t) ω-Z (k,s) ω
  have hi q := (hZ.hasGaussianLaw_eval q).memLp_two
  have hD k : MemLp (D k) 2 P := (hi (k,t)).sub (hi (k,s))
  have hind := gaussian_brownian_increment_independent_joint_past P Z hZ hcov s t hst
  have hDc (k : ι) : P[D k | jointPast Z s] =ᵐ[P] fun _ => (0:ℝ) := by
    have h := conditional_independent_jointPast P Z hm s (D k) ((hm _).sub (hm _))
      (hind.comp (measurable_pi_apply k) measurable_id)
    simpa only [D,gaussian_joint_increment_mean P Z hZ hmean] using h
  have hDD : P[(fun ω => D i ω*D j ω) | jointPast Z s] =ᵐ[P]
      fun _ => if i=j then (t:ℝ)-(s:ℝ) else 0 := by
    have h := conditional_independent_jointPast P Z hm s (fun ω => D i ω*D j ω)
      (((hm _).sub (hm _)).mul ((hm _).sub (hm _)))
      (hind.comp ((measurable_pi_apply i).mul (measurable_pi_apply j)) measurable_id)
    simpa only [D,joint_increment_product_mean P Z hZ hmean hcov i j s t hst] using h
  have hcross (k l : ι) : P[(fun ω => Z (k,s) ω*D l ω) | jointPast Z s] =ᵐ[P]
      fun _ => (0:ℝ) := by
    have h := condExp_mul_of_stronglyMeasurable_left
      (jointPast_adapted Z k s).stronglyMeasurable ((hi (k,s)).integrable_mul (hD l))
      ((hD l).integrable (by norm_num))
    simp only [Pi.mul_def] at h
    filter_upwards [h,hDc l] with ω hω hd
    simpa only [Pi.mul_apply,hd,mul_zero] using hω
  have hself : P[(fun ω => Z (i,s) ω*Z (j,s) ω) | jointPast Z s] =
      fun ω => Z (i,s) ω*Z (j,s) ω :=
    condExp_of_stronglyMeasurable (jointPast_le Z hm s)
      ((jointPast_adapted Z i s).mul (jointPast_adapted Z j s)).stronglyMeasurable
      ((hi (i,s)).integrable_mul (hi (j,s)))
  have he : (fun ω => Z (i,t) ω*Z (j,t) ω-(if i=j then (t:ℝ) else 0)) =
      (fun ω => Z (i,s) ω*Z (j,s) ω) +
      (fun ω => Z (i,s) ω*D j ω) + (fun ω => Z (j,s) ω*D i ω) +
      (fun ω => D i ω*D j ω) - (fun _ => if i=j then (t:ℝ) else 0) := by
    funext ω
    dsimp only [Pi.add_apply,Pi.sub_apply,D]
    ring
  rw [he]
  have h1 := condExp_add ((hi (i,s)).integrable_mul (hi (j,s)))
    ((hi (i,s)).integrable_mul (hD j)) (jointPast Z s)
  have h2 := condExp_add (((hi (i,s)).integrable_mul (hi (j,s))).add
    ((hi (i,s)).integrable_mul (hD j))) ((hi (j,s)).integrable_mul (hD i)) (jointPast Z s)
  have h3 := condExp_add ((((hi (i,s)).integrable_mul (hi (j,s))).add
    ((hi (i,s)).integrable_mul (hD j))).add ((hi (j,s)).integrable_mul (hD i)))
    ((hD i).integrable_mul (hD j)) (jointPast Z s)
  have h4 := condExp_sub (((((hi (i,s)).integrable_mul (hi (j,s))).add
    ((hi (i,s)).integrable_mul (hD j))).add ((hi (j,s)).integrable_mul (hD i))).add
    ((hD i).integrable_mul (hD j))) (integrable_const (if i=j then (t:ℝ) else 0)) (jointPast Z s)
  simp only [Pi.mul_def] at h1 h2 h3 h4
  have hc := condExp_const (jointPast_le Z hm s) (if i=j then (t:ℝ) else 0) (μ := P)
  filter_upwards [h1,h2,h3,h4,hcross i j,hcross j i,hDD] with ω h1 h2 h3 h4 hij hji hdd
  simp only [Pi.add_apply,Pi.sub_apply,hself,hc] at h1 h2 h3 h4 ⊢
  rw [h4,h3,h2,h1,hij,hji,hdd]
  split_ifs <;> ring

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.joint_increment_product_mean
#print axioms Asakura.EndToEnd.gaussian_joint_product_martingale
