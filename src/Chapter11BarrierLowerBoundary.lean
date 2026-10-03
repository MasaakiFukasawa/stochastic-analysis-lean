import Chapter11BarrierStockCoordinates

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.Chapter4
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- The truncated payoff is bounded by the terminal stock; the Gaussian
exponential moment gives v(t,x) <= x, including the discount exactly. -/
theorem barrier_vanilla_le_stock (b K r σ θ y : ℝ)
    (hb : 0<b) (hK : 0<K) (hσ : 0<σ) (hθ : 0<θ) :
    Real.exp (-r*θ)*barrierGaussianAverage b K (r-σ^2/2) σ θ y≤b*Real.exp y := by
  let S := fun z => b*Real.exp (y+(r-σ^2/2)*θ+σ*Real.sqrt θ*z)
  let f := fun z => if y+(r-σ^2/2)*θ+σ*Real.sqrt θ*z<0 then max (S z-K) 0 else 0
  have hSi : Integrable S (gaussianReal 0 1) := by
    convert (integrable_exp_mul_gaussianReal (μ:=0) (v:=1) (σ*Real.sqrt θ)).const_mul (b*Real.exp (y+(r-σ^2/2)*θ)) using 1
    funext z
    simp only [S,Real.exp_add]
    ring
  have hfn z : 0≤f z := by dsimp only [f];split_ifs <;> positivity
  have hfs z : f z≤S z := by
    dsimp only [f]
    split_ifs
    · exact max_le (by linarith) (mul_pos hb (Real.exp_pos _)).le
    · exact (mul_pos hb (Real.exp_pos _)).le
  have hfm : Measurable f := by
    dsimp only [f,S]
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) <;> fun_prop
  have hfi : Integrable f (gaussianReal 0 1) := hSi.mono' hfm.aestronglyMeasurable
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (hfn z)];exact hfs z)
  have he : (∫ z,S z ∂gaussianReal 0 1)=b*Real.exp (y+r*θ) := by
    have hh := congrFun (mgf_fun_id_gaussianReal (μ:=0) (v:=1)) (σ*Real.sqrt θ)
    simp only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add] at hh
    dsimp only [S]
    rw [show (fun z => b*Real.exp (y+(r-σ^2/2)*θ+σ*Real.sqrt θ*z))=
      (fun z => b*Real.exp (y+(r-σ^2/2)*θ)*Real.exp ((σ*Real.sqrt θ)*z)) by funext z;rw [Real.exp_add];ring]
    rw [integral_const_mul,hh,mul_assoc,←Real.exp_add]
    congr 2
    nlinarith [Real.sq_sqrt hθ.le]
  have hh := mul_le_mul_of_nonneg_left (integral_mono hfi hSi hfs) (Real.exp_pos (-r*θ)).le
  rw [he] at hh
  have he' : Real.exp (-r*θ)*(b*Real.exp (y+r*θ))=b*Real.exp y := by
    rw [mul_left_comm,←Real.exp_add]
    congr 2
    ring
  rw [he'] at hh
  exact hh

/-- Both boundary-control bounds for the actual reflected stock price. -/
theorem barrier_stock_price_bounds (b K r σ θ y : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (hθ : 0<θ) (hy : y≤0) :
    0≤barrierStockPrice b K r σ θ (b*Real.exp y) ∧
      barrierStockPrice b K r σ θ (b*Real.exp y)≤b*Real.exp y ∧
      barrierStockPrice b K r σ θ (b*Real.exp y)≤Real.exp (-r*θ)*(b-K) := by
  obtain ⟨hfm,hfn,hfb,hfz⟩ := barrier_log_payoff_bounds b K hb hK hKb
  have hν : (2*r/σ^2-1)*(σ^2*θ)=2*(r-σ^2/2)*θ := by
    have hh := barrier_reflection_parameter r σ hσ.ne'
    linear_combination θ*hh
  have hv : 0<σ^2*θ := by positivity
  have hv0 : (NNReal.mk (σ^2*θ) hv.le)≠0 := by
    intro h;have hh := congrArg (fun x : ℝ≥0 => (x:ℝ)) h;exact hv.ne' hh
  have hbound := barrier_image_integral_bounds (r-σ^2/2) θ (2*r/σ^2-1) y
    (NNReal.mk (σ^2*θ) hv.le) hv0 hν hy (barrierLogPayoff b K) hfm (b-K) (sub_nonneg.mpr hKb.le) hfn hfb hfz
  dsimp only at hbound
  rw [barrier_gaussian_average_pdf b K (r-σ^2/2) σ θ y hσ hθ,
    barrier_gaussian_average_pdf b K (r-σ^2/2) σ θ (-y) hσ hθ] at hbound
  rw [barrier_stock_gaussian_formula b K r σ θ y hb hK hKb hσ hθ]
  refine ⟨mul_nonneg (Real.exp_pos _).le hbound.1,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left hbound.2.1 (Real.exp_pos _).le).trans
      (barrier_vanilla_le_stock b K r σ θ y hb hK hσ hθ)
  · exact mul_le_mul_of_nonneg_left (hbound.2.1.trans hbound.2.2) (Real.exp_pos _).le

/-- The lower stock boundary condition follows by squeezing between 0
and x; no asymptotic expansion of a Gaussian tail is required. -/
theorem barrier_zero_stock_limit (b K r σ θ : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (hθ : 0<θ) :
    Tendsto (barrierStockPrice b K r σ θ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have he : ∀ᶠ x in 𝓝[>] (0:ℝ),0≤barrierStockPrice b K r σ θ x ∧ barrierStockPrice b K r σ θ x≤x := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with x hx hxb
    have hlog : Real.log (x/b)≤0 := (Real.log_neg (div_pos hx hb) ((div_lt_one hb).mpr hxb)).le
    have h := barrier_stock_price_bounds b K r σ θ (Real.log (x/b)) hb hK hKb hσ hθ hlog
    have hx' : b*Real.exp (Real.log (x/b))=x := by rw [Real.exp_log (div_pos hx hb)];field_simp
    rw [hx'] at h
    exact ⟨h.1,h.2.1⟩
  exact squeeze_zero' (he.mono fun x hx => hx.1) (he.mono fun x hx => hx.2) nhdsWithin_le_nhds

end Asakura.Chapter11
