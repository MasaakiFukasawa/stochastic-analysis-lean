import Chapter9GaussianCoefficients
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set Finset
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000

theorem affine_gaussian_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a v amin R : ℝ) (hamin : 0<amin) (ha : amin ≤ a)
    (hv : 0<v) (hv1 : v ≤ 1) (hR : 0 ≤ R) (x y : E) (hy : ‖y‖ ≤ R) :
    Real.exp (-‖y-a • x‖^2/(2*v)) ≤
      Real.exp (R^2/2)*Real.exp (-(amin^2/4)*‖x‖^2) := by
  have han : 0 ≤ a := hamin.le.trans ha
  have hn : a*‖x‖ ≤ R+‖y-a • x‖ := by
    have hh := norm_sub_le y (y-a • x)
    rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_nonneg han] at hh
    linarith
  have hn' : amin*‖x‖ ≤ R+‖y-a • x‖ :=
    (mul_le_mul_of_nonneg_right ha (norm_nonneg x)).trans hn
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ amin*‖x‖) hn'
  have ht : amin^2*‖x‖^2 ≤ 2*R^2+2*‖y-a • x‖^2 := by
    nlinarith [sq_nonneg (R-‖y-a • x‖)]
  have hd : ‖y-a • x‖^2/2 ≤ ‖y-a • x‖^2/(2*v) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  nlinarith

theorem coordinate_norm_le_euclidean {d : ℕ} (x : Fin d → ℝ) :
    ‖x‖ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) i

/-- A uniform Gaussian tail survives when the data variable is measured
with the coordinate norm used for the finite coefficient expansion. -/
theorem coordinate_gaussian_tail {d : ℕ} (a v amin R : ℝ)
    (hamin : 0<amin) (ha : amin ≤ a) (hv : 0<v) (hv1 : v ≤ 1) (hR : 0 ≤ R)
    (x y : Fin d → ℝ) (hy : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))‖ ≤ R) :
    Real.exp (-(∑ i,(y i-a*x i)^2)/(2*v)) ≤
      Real.exp (R^2/2)*Real.exp (-(amin^2/4)*‖x‖^2) := by
  have hh := affine_gaussian_tail a v amin R hamin ha hv hv1 hR
    (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y) hy
  rw [EuclideanSpace.real_norm_sq_eq] at hh
  simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  have hn := coordinate_norm_le_euclidean x
  have hs := mul_self_le_mul_self (norm_nonneg x) hn
  nlinarith [sq_nonneg amin]
end Asakura.Chapter9
