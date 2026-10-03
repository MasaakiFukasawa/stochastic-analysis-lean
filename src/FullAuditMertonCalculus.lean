import FullAuditLogWealth
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000

noncomputable def mertonRate (r μ σ γ : ℝ) :=
  (1-γ)*(r+(μ-r)^2/(2*γ*σ^2))
noncomputable def mertonValue (r μ σ γ T t x : ℝ) :=
  Real.exp (mertonRate r μ σ γ*(T-t))*x^(1-γ)/(1-γ)

theorem merton_value_dx (r μ σ γ T t x : ℝ) (hx : 0 < x) (hγ : γ ≠ 1) :
    HasDerivAt (mertonValue r μ σ γ T t)
      (Real.exp (mertonRate r μ σ γ*(T-t))*x^(-γ)) x := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1-γ) (Or.inl (ne_of_gt hx))).const_mul
    (Real.exp (mertonRate r μ σ γ*(T-t)))).div_const (1-γ)
  convert h using 1
  · rfl
  · rw [show (1:ℝ)-γ-1 = -γ by ring]
    field_simp

theorem merton_value_dxx (r μ σ γ T t x : ℝ) (hx : 0 < x) (hγ : γ ≠ 1) :
    HasDerivAt (fun y => deriv (mertonValue r μ σ γ T t) y)
      (-γ*Real.exp (mertonRate r μ σ γ*(T-t))*x^(-γ-1)) x := by
  have h := (Real.hasDerivAt_rpow_const (p := -γ) (Or.inl (ne_of_gt hx))).const_mul
    (Real.exp (mertonRate r μ σ γ*(T-t)))
  apply HasDerivAt.congr_of_eventuallyEq (by convert h using 1 <;> ring)
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact (merton_value_dx r μ σ γ T t y hy hγ).deriv

theorem merton_value_dt (r μ σ γ T t x : ℝ) :
    HasDerivAt (fun s => mertonValue r μ σ γ T s x)
      (-mertonRate r μ σ γ*Real.exp (mertonRate r μ σ γ*(T-t))*x^(1-γ)/(1-γ)) t := by
  have h := (((((hasDerivAt_const t T).sub (hasDerivAt_id t)).const_mul
    (mertonRate r μ σ γ)).exp).mul_const (x^(1-γ))).div_const (1-γ)
  convert h using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; ring)

theorem merton_rpow_identities (x γ : ℝ) (hx : 0 < x) :
    x*x^(-γ) = x^(1-γ) ∧ x^2*x^(-γ-1) = x^(1-γ) := by
  constructor
  · nth_rw 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx]
    congr 1
  · rw [← Real.rpow_natCast x 2,← Real.rpow_add hx]
    congr 1
    ring

theorem merton_generator_square (r μ σ γ T t x z : ℝ)
    (hx : 0 < x) (hγ : γ ≠ 1) (hγ0 : γ ≠ 0) (hσ : σ ≠ 0) :
    deriv (fun s => mertonValue r μ σ γ T s x) t+
      x*(r+z*(μ-r))*deriv (mertonValue r μ σ γ T t) x+
      σ^2*z^2*x^2/2*deriv (fun y => deriv (mertonValue r μ σ γ T t) y) x =
    -(γ*σ^2/2)*Real.exp (mertonRate r μ σ γ*(T-t))*x^(1-γ)*(z-(μ-r)/(γ*σ^2))^2 := by
  rw [(merton_value_dt r μ σ γ T t x).deriv,(merton_value_dx r μ σ γ T t x hx hγ).deriv,
    (merton_value_dxx r μ σ γ T t x hx hγ).deriv]
  have hp := merton_rpow_identities x γ hx
  calc
    _ = Real.exp (mertonRate r μ σ γ*(T-t))*x^(1-γ)*
        (-mertonRate r μ σ γ/(1-γ)+r+z*(μ-r)-γ*σ^2*z^2/2) := by
      linear_combination (r+z*(μ-r))*Real.exp (mertonRate r μ σ γ*(T-t))*hp.1 +
        (-γ*σ^2*z^2/2)*Real.exp (mertonRate r μ σ γ*(T-t))*hp.2
    _ = _ := by
      dsimp only [mertonRate]
      field_simp
      <;> ring

theorem merton_noise_coefficient (r μ σ γ T t x z : ℝ) (hx : 0 < x) (hγ : γ ≠ 1) :
    σ*z*x*deriv (mertonValue r μ σ γ T t) x =
      Real.exp (mertonRate r μ σ γ*(T-t))*σ*z*x^(1-γ) := by
  rw [(merton_value_dx r μ σ γ T t x hx hγ).deriv]
  linear_combination σ*z*Real.exp (mertonRate r μ σ γ*(T-t))*(merton_rpow_identities x γ hx).1

theorem merton_terminal_utility (r μ σ γ T x : ℝ) :
    mertonValue r μ σ γ T T x = x^(1-γ)/(1-γ) := by
  simp [mertonValue]

end Asakura.FullAudit
