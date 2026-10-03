import Chapter11BarrierStockCoordinates
import Chapter11BarrierEnergy

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

theorem barrier_vanilla_differentiable (b K r σ θ x : ℝ)
    (hb : 0<b) (hK : 0<K) (hσ : 0<σ) (hθ : 0<θ) (hx : 0<x) :
    DifferentiableAt ℝ (barrierVanillaCombination b K r σ θ) x := by
  exact (((bs_call_delta x K r 0 σ θ hx hK hσ hθ).differentiableAt.sub
    (bs_call_delta x b r 0 σ θ hx hb hσ hθ).differentiableAt).sub
    ((barrier_digital_delta b r σ θ x hb.ne' hx.ne').differentiableAt.const_mul (b-K)))

theorem barrier_stock_delta (b K r σ θ x : ℝ)
    (hb : 0<b) (hK : 0<K) (hσ : 0<σ) (hθ : 0<θ) (hx : 0<x) :
    HasDerivAt (barrierStockPrice b K r σ θ)
      (deriv (barrierVanillaCombination b K r σ θ) x+(b/x)^(2*r/σ^2-1)*
        ((2*r/σ^2-1)/x*barrierVanillaCombination b K r σ θ (b^2/x)+
          b^2/x^2*deriv (barrierVanillaCombination b K r σ θ) (b^2/x))) x := by
  exact barrier_price_delta b (2*r/σ^2-1) x hb hx _ _ _
    (barrier_vanilla_differentiable b K r σ θ x hb hK hσ hθ hx).hasDerivAt
    (barrier_vanilla_differentiable b K r σ θ (b^2/x) hb hK hσ hθ (div_pos (sq_pos_of_pos hb) hx)).hasDerivAt

/-- Identify the derivative in the actual Brownian Ito integral with
the stock delta in the manuscript, including the volatility and discount. -/
theorem barrier_brownian_delta_identity (b K r σ T y0 t w : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (ht : t<T) :
    let S := b*Real.exp (y0+(r-σ^2/2)*t+σ*w)
    fderiv ℝ (barrierBrownianPrice b K r σ T y0) ![t,w] (Pi.single 1 1)=
      Real.exp (-r*t)*σ*S*deriv (barrierStockPrice b K r σ (T-t)) S := by
  dsimp only
  let S := b*Real.exp (y0+(r-σ^2/2)*t+σ*w)
  have hS : 0<S := mul_pos hb (Real.exp_pos _)
  have hv : DifferentiableAt ℝ (barrierStockPrice b K r σ (T-t)) S :=
    (barrier_stock_delta b K r σ (T-t) S hb hK hσ (sub_pos.mpr ht) hS).differentiableAt
  have hSd : HasDerivAt (fun w => b*Real.exp (y0+(r-σ^2/2)*t+σ*w)) (σ*S) w := by
    convert (((hasDerivAt_id w).const_mul σ).const_add (y0+(r-σ^2/2)*t)).exp.const_mul b using 1
    · rfl
    · dsimp only [S,id_eq];ring
  have hright := (hv.hasDerivAt.comp w hSd).const_mul (Real.exp (-r*t))
  have hvec : HasDerivAt (fun x : ℝ => ![t,x]) (Pi.single 1 1) w := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using hasDerivAt_const w t
    · change HasDerivAt (fun x : ℝ => x) (1:ℝ) w
      exact hasDerivAt_id w
  have hsmooth : ContDiffAt ℝ 2 (barrierBrownianPrice b K r σ T y0) ![t,w] := (barrier_price_smooth b K r σ T y0 hb hK hKb hσ).contDiffAt
    ((isOpen_lt (continuous_apply 0) continuous_const).mem_nhds (by simpa using ht))
  have hleft := ((hsmooth.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt w hvec
  have he : (fun x => barrierBrownianPrice b K r σ T y0 ![t,x])=
      fun x => Real.exp (-r*t)*barrierStockPrice b K r σ (T-t) (b*Real.exp (y0+(r-σ^2/2)*t+σ*x)) :=
    funext fun x => barrier_brownian_stock_identity b K r σ T y0 t x hb hK hKb hσ ht
  change HasDerivAt (fun x => barrierBrownianPrice b K r σ T y0 ![t,x]) _ w at hleft
  rw [he] at hleft
  have hh := hleft.unique hright
  change _=Real.exp (-r*t)*(deriv (barrierStockPrice b K r σ (T-t)) S*(σ*S)) at hh
  rw [hh]
  ring

end Asakura.Chapter11
