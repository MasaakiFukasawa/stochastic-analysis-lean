import Chapter9GaussianTail

open Set Finset
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The actual logarithm of the OU kernel is smooth on positive times. -/
theorem ou_exponent_smooth {d : ℕ} (x : Fin d → ℝ) :
    ContDiffOn ℝ ∞ (ouExponent x) {z | 0<z.1} := by
  change ContDiffOn ℝ ∞ (fun z => ouExponent x z) {z | 0<z.1}
  simp_rw [ou_exponent_coefficients]
  apply ContDiffOn.sum
  intro j _
  exact contDiffOn_const.mul (ou_coefficient_smooth j)

theorem ou_prefactor_smooth (d : ℕ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × (Fin d → ℝ) =>
      -(d:ℝ)/2*Real.log (2*Real.pi*(1-Real.exp (-2*z.1)))) {z | 0<z.1} := by
  apply ContDiffOn.mul contDiffOn_const
  apply ContDiffOn.log (by fun_prop)
  intro z hz
  exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (ou_variance_positive z.1 hz).ne'

/-- On every compact subset of positive time-space, each actual joint
time-space derivative of the OU kernel is bounded uniformly in its initial
point. Thus no moments of the initial distribution are needed for smoothing. -/
theorem ou_kernel_all_order_compact_bound {d : ℕ}
    (K : Set (ℝ × (Fin d → ℝ))) (hK : IsCompact K) (hKU : K ⊆ {z | 0<z.1})
    (n : ℕ) : ∃ B : ℝ,0 ≤ B ∧ ∀ x z,z∈K →
      ‖iteratedFDerivWithin ℝ n (fun q => Real.exp (ouExponent x q)) {z | 0<z.1} z‖ ≤ B := by
  let U : Set (ℝ × (Fin d → ℝ)) := {z | 0<z.1}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_fst
  obtain ⟨C,hC,hder⟩ := weighted_coefficient_derivative_bound U K hU hK hKU
    ouCoefficient ou_coefficient_smooth ouWeight (fun x : Fin d → ℝ => ‖x‖) ou_weight_bound n
  have hd x z (hz : z∈K) i (_ : 1 ≤ i) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i (ouExponent x) U z‖ ≤ C*(1+‖x‖^2) := by
    rw [show ouExponent x=(fun q => ∑ j,ouWeight j x*ouCoefficient j q) from
      funext (ou_exponent_coefficients x)]
    exact hder x z hz i hi
  obtain ⟨T,hT⟩ := hK.exists_bound_of_continuousOn
    (continuous_fst.continuousOn : ContinuousOn (fun z : ℝ × (Fin d → ℝ) => z.1) K)
  obtain ⟨R0,hR0⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn (fun z : ℝ × (Fin d → ℝ) =>
      (WithLp.toLp 2 z.2 : EuclideanSpace ℝ (Fin d))) K from (by fun_prop))
  let R := max 0 R0
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn ((ou_prefactor_smooth d).continuousOn.mono hKU)
  let amin := Real.exp (-T)
  let A := Real.exp M*Real.exp (R^2/2)
  have htail x z (hz : z∈K) : Real.exp (ouExponent x z) ≤ A*Real.exp (-(amin^2/4)*‖x‖^2) := by
    have ht : z.1 ≤ T := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hT z hz)
    have ha : amin ≤ Real.exp (-z.1) := Real.exp_le_exp.mpr (by linarith)
    have hv := ou_variance_positive z.1 (hKU hz)
    have hv1 : 1-Real.exp (-2*z.1) ≤ 1 := by linarith [Real.exp_pos (-2*z.1)]
    have hy : ‖(WithLp.toLp 2 z.2 : EuclideanSpace ℝ (Fin d))‖ ≤ R :=
      (hR0 z hz).trans (le_max_right _ _)
    have hh := coordinate_gaussian_tail (Real.exp (-z.1)) (1-Real.exp (-2*z.1)) amin R
      (Real.exp_pos _) ha hv hv1 (le_max_left _ _) x z.2 hy
    have hm : -(d:ℝ)/2*Real.log (2*Real.pi*(1-Real.exp (-2*z.1))) ≤ M :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM z hz)
    unfold ouExponent
    rw [Real.exp_sub]
    rw [div_eq_mul_inv,←Real.exp_neg,show -((∑ i,(z.2 i-Real.exp (-z.1)*x i)^2)/
      (2*(1-Real.exp (-2*z.1))))= -(∑ i,(z.2 i-Real.exp (-z.1)*x i)^2)/
      (2*(1-Real.exp (-2*z.1))) by ring]
    calc
      _ ≤ Real.exp M*(Real.exp (R^2/2)*Real.exp (-(amin^2/4)*‖x‖^2)) :=
        mul_le_mul (Real.exp_le_exp.mpr hm) hh (Real.exp_pos _).le (Real.exp_pos _).le
      _ = _ := by dsimp [A]; ring
  exact exponential_quadratic_all_order_bound U K hU hKU ouExponent (fun x => ‖x‖)
    norm_nonneg n C A (amin^2/4) hC (by dsimp [A]; positivity)
    (by dsimp [amin]; positivity) ou_exponent_smooth hd htail
end Asakura.Chapter9
