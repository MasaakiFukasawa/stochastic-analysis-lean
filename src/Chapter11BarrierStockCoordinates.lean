import Chapter11BarrierCallCombination
import Chapter11BarrierMovingEndpoint

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.Chapter4
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

noncomputable def barrierVanillaCombination (b K r σ θ x : ℝ) : ℝ :=
  bsCall K r 0 σ x θ-bsCall b r 0 σ x θ-(b-K)*digitalPrice b r σ θ x

noncomputable def barrierStockPrice (b K r σ θ x : ℝ) : ℝ :=
  barrierVanillaCombination b K r σ θ x-(b/x)^(2*r/σ^2-1)*barrierVanillaCombination b K r σ θ (b^2/x)

/-- The exact formula in the manuscript, expressed in log-stock
coordinates. Both calls and the digital term are actual Gaussian prices. -/
theorem barrier_stock_gaussian_formula (b K r σ θ y : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (hθ : 0<θ) :
    barrierStockPrice b K r σ θ (b*Real.exp y)=Real.exp (-r*θ)*
      (barrierGaussianAverage b K (r-σ^2/2) σ θ y-
        Real.exp (-(2*r/σ^2-1)*y)*barrierGaussianAverage b K (r-σ^2/2) σ θ (-y)) := by
  have hv y : barrierVanillaCombination b K r σ θ (b*Real.exp y)=
      Real.exp (-r*θ)*barrierGaussianAverage b K (r-σ^2/2) σ θ y :=
    (barrier_gaussian_call_combination b K r σ θ y hb hK hKb hσ hθ).symm
  have hz : b^2/(b*Real.exp y)=b*Real.exp (-y) := by
    rw [Real.exp_neg]
    field_simp
  have hw : (b/(b*Real.exp y))^(2*r/σ^2-1)=Real.exp (-(2*r/σ^2-1)*y) := by
    have he : b/(b*Real.exp y)=Real.exp (-y) := by rw [Real.exp_neg];field_simp
    rw [he,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    congr 1
    ring
  dsimp only [barrierStockPrice]
  rw [hz,hw,hv,hv]
  ring

/-- The Brownian-coordinate solution used in the stochastic proof is
exactly the discounted price printed as a combination of Black--Scholes
solutions, along the actual geometric stock coordinate. -/
theorem barrier_brownian_stock_identity (b K r σ T y0 t w : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (ht : t<T) :
    barrierBrownianPrice b K r σ T y0 ![t,w]=
      Real.exp (-r*t)*barrierStockPrice b K r σ (T-t)
        (b*Real.exp (y0+(r-σ^2/2)*t+σ*w)) := by
  rw [barrier_brownian_gaussian_formula b K r σ T y0 t w hσ ht,
    barrier_stock_gaussian_formula b K r σ (T-t) _ hb hK hKb hσ (sub_pos.mpr ht)]
  rw [←mul_assoc,←Real.exp_add]
  congr 2
  ring

end Asakura.Chapter11
