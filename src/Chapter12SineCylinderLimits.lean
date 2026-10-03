import Chapter12CylinderUnbounded
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The precise two limits printed in the nonboundedness example, for the
actual cylinder values and their derivatives. The index n+1 avoids division
by zero and is the same sequence with its first index shifted. -/
theorem sine_cylinder_limits {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (h : H) (hh : ‖h‖ = 1) :
    let c := fun n : ℕ => sineSmoothCylinder h (n+1) (by positivity)
    Tendsto (fun n => (c n).valueLp P W S hS hcore 2 (by simp)) atTop (𝓝 0) ∧
      (∀ n, ‖(c n).gradientLp P W S hS hcore 2 (by simp)‖^2 =
        (1+Real.exp (-2*((n:ℝ)+1)^2))/2) ∧
      Tendsto (fun n => ‖(c n).gradientLp P W S hS hcore 2 (by simp)‖^2) atTop (𝓝 (1/2)) := by
  let c := fun n : ℕ => sineSmoothCylinder h (n+1) (by positivity)
  have hb (n : ℕ) : ‖(c n).valueLp P W S hS hcore 2 (by simp)‖ ≤ 1/((n:ℝ)+1) := by
    have he := Lp.norm_le_of_ae_bound (f := (c n).valueLp P W S hS hcore 2 (by simp))
      (C := 1/((n:ℝ)+1)) (by positivity) (by
        filter_upwards [((c n).value_memLp P W S hS hcore 2 (by simp)).coeFn_toLp] with w hw
        dsimp only [SmoothCylinder.valueLp]
        rw [hw]
        change |Real.sin (((n:ℝ)+1)*W h w)/((n:ℝ)+1)| ≤ _
        rw [abs_div,abs_of_pos (by positivity : 0 < (n:ℝ)+1)]
        exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity))
    simpa [measureUnivNNReal] using he
  have hv : Tendsto (fun n => (c n).valueLp P W S hS hcore 2 (by simp)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) hb tendsto_one_div_add_atTop_nhds_zero_nat
  have hlaw : HasLaw (W h : Ω → ℝ) (gaussianReal 0 1) P := by
    have he : (⟨‖h‖^2,sq_nonneg _⟩ : ℝ≥0) = 1 := by
      apply Subtype.ext
      change ‖h‖^2 = (1:ℝ)
      rw [hh]
      norm_num
    simpa only [he] using wiener_gaussian_law_from_dense_core P W S hS hcore h
  have hg (n : ℕ) : ‖(c n).gradientLp P W S hS hcore 2 (by simp)‖^2 =
      (1+Real.exp (-2*((n:ℝ)+1)^2))/2 := by
    rw [L2_norm_sq_integral]
    calc
      _ = ∫ w,(Real.cos (((n:ℝ)+1)*W h w))^2 ∂P := by
        apply integral_congr_ae
        filter_upwards [((c n).gradient_memLp P W S hS hcore 2 (by simp)).coeFn_toLp] with w hw
        dsimp only [SmoothCylinder.gradientLp]
        rw [hw]
        change ‖(sineSmoothCylinder h ((n:ℝ)+1) (by positivity)).gradient P W w‖^2 = _
        rw [sine_cylinder_gradient,norm_smul,hh,mul_one,Real.norm_eq_abs,sq_abs]
      _ = ∫ z,(Real.cos (((n:ℝ)+1)*z))^2 ∂gaussianReal 0 1 :=
        hlaw.integral_comp (f := fun z : ℝ => (Real.cos (((n:ℝ)+1)*z))^2) (by fun_prop)
      _ = _ := gaussian_cos_square _
  refine ⟨hv,hg,?_⟩
  have ht2 : Tendsto (fun n : ℕ => 2*((n:ℝ)+1)^2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro R
    filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (max R 1))] with n hn
    have hR := le_max_left R (1:ℝ)
    have h1 := le_max_right R (1:ℝ)
    nlinarith [sq_nonneg (n:ℝ)]
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp ht2
  have hlim := ((tendsto_const_nhds (x := (1:ℝ))).add he).div_const 2
  change Tendsto (fun n => ‖(c n).gradientLp P W S hS hcore 2 (by simp)‖^2) atTop (𝓝 (1/2))
  simp_rw [hg]
  simpa only [Function.comp_apply,neg_mul,add_zero] using hlim

end Asakura.Chapter12
