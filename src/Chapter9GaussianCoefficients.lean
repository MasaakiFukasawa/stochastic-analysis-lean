import Chapter9PolynomialCoefficients
import Chapter9GaussianKernel
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Set Finset
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

noncomputable def ouExponent {d : ℕ} (x : Fin d → ℝ) (z : ℝ × (Fin d → ℝ)) : ℝ :=
  -(d:ℝ)/2*Real.log (2*Real.pi*(1-Real.exp (-2*z.1)))-
    (∑ i,(z.2 i-Real.exp (-z.1)*x i)^2)/(2*(1-Real.exp (-2*z.1)))

noncomputable def ouCoefficient {d : ℕ} (j : Option (Fin d × Bool))
    (z : ℝ × (Fin d → ℝ)) : ℝ :=
  match j with
  | none => -(d:ℝ)/2*Real.log (2*Real.pi*(1-Real.exp (-2*z.1)))-
      (∑ i,(z.2 i)^2)/(2*(1-Real.exp (-2*z.1)))
  | some (i,false) => Real.exp (-z.1)*z.2 i/(1-Real.exp (-2*z.1))
  | some (_,true) => -(Real.exp (-z.1))^2/(2*(1-Real.exp (-2*z.1)))

noncomputable def ouWeight {d : ℕ} (j : Option (Fin d × Bool)) (x : Fin d → ℝ) : ℝ :=
  match j with
  | none => 1
  | some (i,false) => x i
  | some (i,true) => (x i)^2

theorem ou_coefficient_smooth {d : ℕ} (j : Option (Fin d × Bool)) :
    ContDiffOn ℝ ∞ (ouCoefficient j) {z | 0<z.1} := by
  have hv (z : ℝ × (Fin d → ℝ)) (hz : z∈{q : ℝ × (Fin d → ℝ) | 0<q.1}) :
      1-Real.exp (-2*z.1) ≠ 0 := (ou_variance_positive z.1 hz).ne'
  have hp (z : ℝ × (Fin d → ℝ)) (hz : z∈{q : ℝ × (Fin d → ℝ) | 0<q.1}) :
      2*Real.pi*(1-Real.exp (-2*z.1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (hv z hz)
  cases j with
  | none =>
    unfold ouCoefficient
    apply ContDiffOn.sub
    · apply ContDiffOn.mul contDiffOn_const
      exact ContDiffOn.log (by fun_prop) hp
    · apply ContDiffOn.div (by fun_prop) (by fun_prop)
      exact fun z hz => mul_ne_zero (by norm_num) (hv z hz)
  | some j =>
    rcases j with ⟨i,b⟩
    cases b <;> unfold ouCoefficient
    · exact ContDiffOn.div (by fun_prop) (by fun_prop) hv
    · apply ContDiffOn.div (by fun_prop) (by fun_prop)
      exact fun z hz => mul_ne_zero (by norm_num) (hv z hz)

theorem ou_weight_bound {d : ℕ} (j : Option (Fin d × Bool)) (x : Fin d → ℝ) :
    |ouWeight j x| ≤ 1+‖x‖^2 := by
  cases j with
  | none => simp only [ouWeight,abs_one]; nlinarith [sq_nonneg ‖x‖]
  | some j =>
    rcases j with ⟨i,b⟩
    have hh : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    cases b
    · change |x i| ≤ 1+‖x‖^2
      nlinarith [sq_nonneg (‖x‖-1)]
    · change |(x i)^2| ≤ 1+‖x‖^2
      rw [abs_of_nonneg (sq_nonneg _)]
      have hs := mul_self_le_mul_self (abs_nonneg (x i)) hh
      nlinarith [sq_abs (x i)]

theorem ou_exponent_coefficients {d : ℕ} (x : Fin d → ℝ) (z : ℝ × (Fin d → ℝ)) :
    ouExponent x z = ∑ j,ouWeight j x*ouCoefficient j z := by
  simp only [Fintype.sum_option,Fintype.sum_prod_type,Fintype.sum_bool,ouWeight,ouCoefficient,one_mul]
  unfold ouExponent
  rw [sum_div, sum_div]
  have he (i : Fin d) :
      (z.2 i-Real.exp (-z.1)*x i)^2/(2*(1-Real.exp (-2*z.1))) =
      (z.2 i)^2/(2*(1-Real.exp (-2*z.1))) -
        ((x i)^2*(-(Real.exp (-z.1))^2/(2*(1-Real.exp (-2*z.1))))+
          x i*(Real.exp (-z.1)*z.2 i/(1-Real.exp (-2*z.1)))) := by
    simp only [div_mul_eq_div_div]
    ring
  simp_rw [he]
  rw [sum_sub_distrib]
  ring
end Asakura.Chapter9
