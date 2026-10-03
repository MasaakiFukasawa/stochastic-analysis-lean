import Chapter12BasketGreekDirections

open Matrix Finset
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Shifting the Gaussian vector in the inverse-volatility direction is
exactly a multiplicative change of a single initial stock price. -/
theorem basket_log_price_shift {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det≠0)
    (x b z : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    (fun k => x k*Real.exp (b k+∑ j,A k j*(t*(A⁻¹) j i+z j)))=
      (fun k => (if k=i then x i*Real.exp t else x k)*Real.exp (b k+∑ j,A k j*z j)) := by
  funext k
  have he : (∑ j,A k j*(t*(A⁻¹) j i+z j))=
      t*(if k=i then 1 else 0)+(∑ j,A k j*z j) := by
    rw [← basket_delta_matrix_direction A hA i k,Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [he]
  by_cases hk : k=i
  · subst k
    simp only [ite_true,mul_one]
    rw [show b i+(t+∑ j,A i j*z j)=t+(b i+∑ j,A i j*z j) by ring,Real.exp_add]
    ring
  · simp [hk]

end Asakura.Chapter12
