import Chapter12FiniteDivergence

namespace Asakura.Chapter12

/-- The quotient correction in the Asian delta is not optional: the chosen
integrand is anticipating. -/
theorem asian_delta_weight (x σ I₀ I₁ I₂ W : ℝ)
    (hx : x ≠ 0) (hσ : σ ≠ 0) (hI : I₁ ≠ 0) :
    (I₀/(x*σ*I₁))*W - (1/(x*σ))*
      ((σ*I₁)/I₁-I₀*(σ*I₂)/I₁^2) =
      (1/x)*(I₀*W/(σ*I₁)-1+I₀*I₂/I₁^2) := by
  field_simp
  <;> ring

/-- Integrating the derivative of J0 gives sigma J1 + I1. The latter
contributes the -1/sigma term in the printed vega. -/
theorem asian_vega_weight (σ I₁ I₂ J₀ J₁ W : ℝ)
    (hσ : σ ≠ 0) (hI : I₁ ≠ 0) :
    (J₀/(σ*I₁))*W - (1/σ)*
      ((σ*J₁+I₁)/I₁-J₀*(σ*I₂)/I₁^2) =
      J₀*W/(σ*I₁)-J₁/I₁-1/σ+J₀*I₂/I₁^2 := by
  field_simp
  <;> ring

theorem asian_delta_direction (x σ T I₀ I₁ : ℝ)
    (hσ : σ ≠ 0) (hI : I₁ ≠ 0) :
    (σ*I₁/T)*(I₀/(x*σ*I₁)) = I₀/(x*T) := by
  field_simp
  <;> ring

theorem asian_vega_direction (σ T I₁ J₀ : ℝ)
    (hσ : σ ≠ 0) (hI : I₁ ≠ 0) :
    (σ*I₁/T)*(J₀/(σ*I₁)) = J₀/T := by
  field_simp
  <;> ring

/-- The pathwise derivative of the Black--Scholes stock with respect to
volatility, holding the Brownian path fixed. -/
theorem stock_volatility_derivative (x r t w σ : ℝ) :
    HasDerivAt (fun a : ℝ => x*Real.exp ((r-a^2/2)*t+a*w))
      (x*Real.exp ((r-σ^2/2)*t+σ*w)*(w-σ*t)) σ := by
  have h := (((hasDerivAt_const σ r).sub
    ((hasDerivAt_id σ).pow 2 |>.div_const 2)).mul_const t |>.add
    ((hasDerivAt_id σ).mul_const w)).exp.const_mul x
  convert h using 1
  · ext a
    simp only [id_eq,Pi.add_apply,Pi.sub_apply,Pi.pow_apply]
  · simp only [id_eq,Pi.add_apply,Pi.sub_apply,Pi.pow_apply]
    ring

end Asakura.Chapter12
