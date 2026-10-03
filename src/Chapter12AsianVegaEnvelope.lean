import Chapter12StockPathEnvelope
import Chapter12AsianParameterDerivative

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem stock_volatility_derivative_uniform_bound (x r T L σ : ℝ)
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hσ : |σ| ≤ L)
    (f : C(Icc (0:ℝ) T,ℝ)) (t : Icc (0:ℝ) T) :
    |stockPathValue x σ r T f t * (f t-σ*t.val)| ≤
      (|x| *Real.exp ((|r| +L^2/2)*T)*(1+L*T))*Real.exp ((L+1)*‖f‖) := by
  have hs2 : σ^2 ≤ L^2 := by nlinarith [sq_abs σ,abs_nonneg σ]
  have hdr : |r-σ^2/2| ≤ |r| +L^2/2 := by
    calc
      _ ≤ |r| +|σ^2/2| := by simpa using abs_sub_le r 0 (σ^2/2)
      _ ≤ _ := by rw [abs_of_nonneg (by positivity : 0 ≤ σ^2/2)]; linarith
  have he : |r-σ^2/2| *T+|σ| *‖f‖ ≤ (|r| +L^2/2)*T+L*‖f‖ :=
    add_le_add (mul_le_mul_of_nonneg_right hdr hT) (mul_le_mul_of_nonneg_right hσ (norm_nonneg _))
  have hS : |stockPathValue x σ r T f t| ≤
      |x| *Real.exp ((|r| +L^2/2)*T+L*‖f‖) :=
    (stock_path_upper_bound x σ r T f t).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (abs_nonneg _))
  have hb : |f t-σ*t.val| ≤ ‖f‖+L*T := by
    calc
      _ ≤ |f t| +|σ*t.val| := by simpa using abs_sub_le (f t) 0 (σ*t.val)
      _ ≤ ‖f‖+L*T := by
        rw [abs_mul,abs_of_nonneg t.property.1]
        exact add_le_add (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm t)
          (mul_le_mul hσ t.property.2 t.property.1 hL)
  have hexp : ‖f‖+L*T ≤ (1+L*T)*Real.exp ‖f‖ := by
    have h1 : 1 ≤ Real.exp ‖f‖ := Real.one_le_exp (norm_nonneg _)
    have h2 := Real.add_one_le_exp ‖f‖
    nlinarith [mul_nonneg hL hT]
  rw [abs_mul]
  calc
    _ ≤ (|x| *Real.exp ((|r| +L^2/2)*T+L*‖f‖))*((1+L*T)*Real.exp ‖f‖) :=
      mul_le_mul hS (hb.trans hexp) (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [Real.exp_add]
      have hh : Real.exp ((L+1)*‖f‖) = Real.exp (L*‖f‖)*Real.exp ‖f‖ := by rw [add_mul,one_mul,Real.exp_add]
      rw [hh]
      ring

end Asakura.Chapter12
