import Chapter12GaussianScaleScore

open Finset
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Uniform Gaussian decay when a positive scale varies in a compact
neighborhood. This is the domination used for Borel-payoff vega. -/
theorem gaussian_scale_quadratic_lower (s u z k : ℝ) (hs : 0<s)
    (hu : s/2≤u) (hu' : u≤2*s) :
    z^2/(8*s^2)-s^2*k^2≤(z/u+u*k/2)^2 := by
  have hup : 0<u := by linarith
  have ha : z^2/(8*s^2)≤(z/u)^2/2 := by
    rw [div_pow,div_div]
    apply div_le_div_of_nonneg_left (sq_nonneg z) (by positivity)
    nlinarith [sq_nonneg (2*s-u)]
  have hb : (u*k/2)^2≤s^2*k^2 := by
    rw [div_pow,mul_pow]
    have hu2 : u^2≤4*s^2 := by nlinarith [sq_nonneg (2*s-u)]
    have hh := mul_le_mul_of_nonneg_right hu2 (sq_nonneg k)
    nlinarith
  have hc : (z/u)^2/2-(u*k/2)^2≤(z/u+u*k/2)^2 := by
    nlinarith [sq_nonneg (z/u+2*(u*k/2))]
  linarith

theorem gaussian_scale_exponential_envelope {d : ℕ} (s u : ℝ) (hs : 0<s)
    (hu : s/2≤u) (hu' : u≤2*s) (z k : Fin d → ℝ) :
    Real.exp (-(∑ i,(z i/u+u*k i/2)^2)/2)≤
      Real.exp (s^2*(∑ i,(k i)^2)/2)*Real.exp (-(∑ i,(z i)^2)/(16*s^2)) := by
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin d))) =>
    gaussian_scale_quadratic_lower s u (z i) (k i) hs hu hu')
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : (∑ i,((z i)^2/(8*s^2)-s^2*(k i)^2))=
      (∑ i,(z i)^2)/(8*s^2)-s^2*(∑ i,(k i)^2) := by
    simp only [Finset.sum_sub_distrib,div_eq_mul_inv,Finset.sum_mul,Finset.mul_sum]
  rw [he] at hh
  have he2 : (∑ i,(z i)^2)/(16*s^2)=((∑ i,(z i)^2)/(8*s^2))/2 := by ring
  simp only [neg_div]
  rw [he2]
  linarith

end Asakura.Chapter12
