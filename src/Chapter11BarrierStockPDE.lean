import Chapter11BarrierStockCoordinates
import Chapter11ScaledHeatPrice

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ContDiff
namespace Asakura.Chapter11
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

theorem image_heat_equation (f : ℝ → ℝ) (hf : Measurable f)
    (K ν : ℝ) (hK : 0≤K) (hn : ∀ z,0≤f z) (hb : ∀ z,f z≤K) :
    ∀ t y,0<t → deriv (fun s => imageHeat f ν (s,y)) t=(1/2:ℝ)*deriv (deriv (fun a => imageHeat f ν (t,a))) y := by
  have hb' z : f z≤K*(1+Real.exp ((0:ℝ)*z)) := by simpa using (hb z).trans (by linarith : K≤K*(1+1))
  obtain ⟨hgm,hgn,hgb⟩ := reflected_payoff_exponential_bound f hf K ν hK hn hb
  have hF := exponential_payoff_heat_smooth f hf hn K 0 hK hb'
  have hG := exponential_payoff_heat_smooth _ hgm hgn K (-ν) hK hgb
  exact heat_difference_equation _ _ hF hG
    (fun t y ht => (exponential_payoff_heat_equation f hf hn K 0 hK hb' t y ht).deriv)
    (fun t y ht => (exponential_payoff_heat_equation _ hgm hgn K (-ν) hK hgb t y ht).deriv)

theorem barrier_stock_heat_identity (b K r σ θ x : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (hθ : 0<θ) (hx : 0<x) :
    barrierStockPrice b K r σ θ x=
      heatPrice (imageHeat (barrierLogPayoff b K) (2*r/σ^2-1)) r σ θ (x/b) := by
  have hx' : b*Real.exp (Real.log (x/b))=x := by rw [Real.exp_log (div_pos hx hb)];field_simp
  have hh := barrier_stock_gaussian_formula b K r σ θ (Real.log (x/b)) hb hK hKb hσ hθ
  rw [hx'] at hh
  have hν : (2*r/σ^2-1)*(σ^2*θ)=2*(r-σ^2/2)*θ := by
    have h := barrier_reflection_parameter r σ hσ.ne'
    linear_combination θ*h
  have hi := image_heat_gaussian_formula (barrierLogPayoff b K) (r-σ^2/2) θ (2*r/σ^2-1) (Real.log (x/b)) (σ^2*θ) (by positivity) hν
  rw [barrier_gaussian_average_pdf b K (r-σ^2/2) σ θ (Real.log (x/b)) hσ hθ,
    barrier_gaussian_average_pdf b K (r-σ^2/2) σ θ (-Real.log (x/b)) hσ hθ] at hi
  rw [hh]
  dsimp only [heatPrice]
  rw [hi]

/-- Smoothness and the actual Black--Scholes equation for the exact
call/digital combination in stock coordinates. -/
theorem barrier_stock_price_pde (b K r σ θ x : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (hθ : 0<θ) (hx : 0<x) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => barrierStockPrice b K r σ q.1 q.2) (θ,x) ∧
      deriv (fun t => barrierStockPrice b K r σ t x) θ=
        r*x*deriv (barrierStockPrice b K r σ θ) x+
        σ^2*x^2/2*deriv (deriv (barrierStockPrice b K r σ θ)) x-r*barrierStockPrice b K r σ θ x := by
  let F := imageHeat (barrierLogPayoff b K) (2*r/σ^2-1)
  obtain ⟨hfm,hfn,hfb,hfz⟩ := barrier_log_payoff_bounds b K hb hK hKb
  have hF := (image_heat_smooth_harmonic _ hfm (b-K) (2*r/σ^2-1) 1 σ 1 0
    (sub_nonneg.mpr hKb.le) hfn hfb hσ.ne').1
  have hheat := image_heat_equation _ hfm (b-K) (2*r/σ^2-1) (sub_nonneg.mpr hKb.le) hfn hfb
  have heq : (fun q : ℝ × ℝ => barrierStockPrice b K r σ q.1 q.2)=ᶠ[𝓝 (θ,x)]
      fun q => heatPrice F r σ q.1 (q.2/b) := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hθ,
      (isOpen_lt continuous_const continuous_snd).mem_nhds hx] with q hqθ hqx
    exact barrier_stock_heat_identity b K r σ q.1 q.2 hb hK hKb hσ hqθ hqx
  have hcomp : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => heatPrice F r σ q.1 (q.2/b)) (θ,x) := by
    have hmap : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => (q.1,q.2/b)) (θ,x) := contDiffAt_fst.prodMk (contDiffAt_snd.div_const b)
    exact (heat_price_joint_smooth F hF r σ θ (x/b) hσ.ne' hθ (div_pos hx hb)).comp (θ,x) hmap
  refine ⟨hcomp.congr_of_eventuallyEq heq,?_⟩
  have ht : (fun t => barrierStockPrice b K r σ t x)=ᶠ[𝓝 θ] fun t => heatPrice F r σ t (x/b) := by
    filter_upwards [eventually_gt_nhds hθ] with t ht
    exact barrier_stock_heat_identity b K r σ t x hb hK hKb hσ ht hx
  have hx' : barrierStockPrice b K r σ θ=ᶠ[𝓝 x] fun y => heatPrice F r σ θ (y/b) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact barrier_stock_heat_identity b K r σ θ y hb hK hKb hσ hθ hy
  rw [ht.deriv_eq,hx'.deriv_eq,hx'.deriv.deriv_eq,
    barrier_stock_heat_identity b K r σ θ x hb hK hKb hσ hθ hx]
  exact scaled_heat_price_equation F hF hheat b r σ θ x hb hσ.ne' hθ hx

/-- The time-to-maturity equation above has the backward sign printed
in the book after theta = T-t. -/
theorem barrier_stock_backward_equation (b K r σ T t x : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (ht : t<T) (hx : 0<x) :
    deriv (fun s => barrierStockPrice b K r σ (T-s) x) t+
      r*x*deriv (barrierStockPrice b K r σ (T-t)) x+
      σ^2*x^2/2*deriv (deriv (barrierStockPrice b K r σ (T-t))) x-
      r*barrierStockPrice b K r σ (T-t) x=0 := by
  obtain ⟨hs,hP⟩ := barrier_stock_price_pde b K r σ (T-t) x hb hK hKb hσ (sub_pos.mpr ht) hx
  have htime : DifferentiableAt ℝ (fun a => barrierStockPrice b K r σ a x) (T-t) :=
    ((hs.comp (T-t) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  have hd := htime.hasDerivAt.comp t ((hasDerivAt_const t T).sub (hasDerivAt_id t))
  have he : deriv (fun s => barrierStockPrice b K r σ (T-s) x) t= -deriv (fun s => barrierStockPrice b K r σ s x) (T-t) := by
    simpa only [Function.comp_def,Pi.sub_apply,id_eq,zero_sub,mul_neg_one] using hd.deriv
  rw [he,hP]
  ring

end Asakura.Chapter11
