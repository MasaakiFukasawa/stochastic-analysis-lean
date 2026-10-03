import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

open Finset
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Differentiating a translated Gaussian density gives its linear score.
No derivative of the payoff appears in this identity. -/
theorem gaussian_shift_density_derivative {ι : Type*} [Fintype ι]
    (C : ℝ) (z q : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => C*Real.exp (-(∑ i,(z i-s*q i)^2)/2))
      ((C*Real.exp (-(∑ i,(z i-t*q i)^2)/2))*(∑ i,(z i-t*q i)*q i)) t := by
  have h i : HasDerivAt (fun s : ℝ => (z i-s*q i)^2)
      (2*(z i-t*q i)*(-q i)) t := by
    convert ((hasDerivAt_const t (z i)).sub ((hasDerivAt_id t).mul_const (q i))).pow 2 using 1 <;> (try funext s) <;> (try dsimp) <;> ring
  have hh := (((HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)).neg.div_const 2).exp).const_mul C
  have he : -(∑ i,2*(z i-t*q i)*(-q i))/2=∑ i,(z i-t*q i)*q i := by
    simp only [div_eq_mul_inv,← Finset.sum_neg_distrib,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [Pi.neg_apply] at hh
  convert hh using 1
  rw [he]
  ring

/-- A second direction contributes the negative covariance correction
appearing in the gamma weight. -/
theorem gaussian_shift_score_derivative {ι : Type*} [Fintype ι]
    (C : ℝ) (z q v : ι → ℝ) (t : ℝ) :
    HasDerivAt
      (fun s => (C*Real.exp (-(∑ i,(z i-s*v i)^2)/2))*(∑ i,(z i-s*v i)*q i))
      ((C*Real.exp (-(∑ i,(z i-t*v i)^2)/2))*
        ((∑ i,(z i-t*v i)*v i)*(∑ i,(z i-t*v i)*q i)-(∑ i,v i*q i))) t := by
  have h i : HasDerivAt (fun s : ℝ => (z i-s*v i)*q i) (-v i*q i) t := by
    convert ((hasDerivAt_const t (z i)).sub ((hasDerivAt_id t).mul_const (v i))).mul_const (q i) using 1 <;> (try funext s) <;> (try dsimp) <;> ring
  have hh := (gaussian_shift_density_derivative C z v t).mul
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i))
  convert hh using 1
  have he : (∑ i,-v i*q i)= -(∑ i,v i*q i) := by simp only [neg_mul,Finset.sum_neg_distrib]
  rw [he]
  ring

end Asakura.Chapter12
