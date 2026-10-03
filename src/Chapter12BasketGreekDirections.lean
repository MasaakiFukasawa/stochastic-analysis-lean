import Chapter12BasketMatrixHedge
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

open Matrix Finset
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The inverse-volatility direction isolates one stock, including the
case of a nonsymmetric volatility matrix. -/
theorem basket_delta_matrix_direction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det≠0) (i k : ι) :
    (∑ j,A k j*(A⁻¹) j i) = if k=i then 1 else 0 := by
  have he := congrArg (fun M : Matrix ι ι ℝ => M k i)
    (Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA))
  simpa only [Matrix.mul_apply,Matrix.one_apply] using he

/-- The Gaussian score covariance is the inverse covariance matrix. -/
theorem basket_gamma_inverse_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) :
    (∑ k,(A⁻¹) k i*(A⁻¹) k j)=((A*A.transpose)⁻¹) i j := by
  rw [Matrix.mul_inv_rev,← Matrix.transpose_nonsing_inv]
  rfl

/-- The common anticipating direction used for proportional volatility
changes has the required directional effect on every asset. -/
theorem basket_vega_matrix_direction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det≠0) (w d : ι → ℝ)
    (s T : ℝ) (hs : s≠0) (hT : T≠0) :
    (s*T) • A.mulVec (fun i => w i/(s*T)-(A⁻¹.mulVec d) i)=
      A.mulVec w-(s*T) • d := by
  have he : (fun i => w i/(s*T)-(A⁻¹.mulVec d) i)=
      (s*T)⁻¹ • w-A⁻¹.mulVec d := by
    ext i
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [he,Matrix.mulVec_sub,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),Matrix.one_mulVec,
    smul_sub,smul_smul,mul_inv_cancel₀ (mul_ne_zero hs hT),one_smul]

/-- Differentiation of the explicit Black--Scholes terminal stock with
respect to the common volatility scale. -/
theorem basket_stock_scale_derivative (x r T a z s : ℝ) :
    HasDerivAt (fun u => x*Real.exp ((r-u^2*a/2)*T+u*z))
      ((x*Real.exp ((r-s^2*a/2)*T+s*z))*(z-s*a*T)) s := by
  have hpow := (hasDerivAt_id s).pow 2
  have he := (((hasDerivAt_const s r).sub ((hpow.mul_const a).div_const 2)).mul_const T).add
    ((hasDerivAt_id s).mul_const z)
  have hh := he.exp.const_mul x
  convert hh using 1 <;> (try funext u) <;> (try dsimp) <;> ring

end Asakura.Chapter12
