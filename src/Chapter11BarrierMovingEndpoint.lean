import Chapter11BarrierConstructed
import Chapter11BarrierEndpoint

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace Asakura.Chapter11
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem barrier_gaussian_average_pdf (b K a σ θ y : ℝ) (hσ : 0<σ) (hθ : 0<θ) :
    (∫ z,barrierLogPayoff b K z*gaussianPDFReal (y+a*θ) (NNReal.mk (σ^2*θ) (by positivity)) z)=
      barrierGaussianAverage b K a σ θ y := by
  have hm : Measurable (barrierLogPayoff b K) := by
    apply Measurable.ite measurableSet_Iio <;> fun_prop
  have hh := heat_gaussian_representation (barrierLogPayoff b K) hm (σ^2*θ) (y+a*θ) (by positivity)
  simp_rw [heat_log_kernel_pdf _ _ _ (show 0<σ^2*θ by positivity)] at hh
  rw [hh]
  dsimp only [barrierGaussianAverage,barrierLogPayoff]
  simp only [Real.sqrt_mul (sq_nonneg σ),Real.sqrt_sq_eq_abs,abs_of_pos hσ]

theorem barrier_brownian_gaussian_formula (b K r σ T y0 t x : ℝ) (hσ : 0<σ) (ht : t<T) :
    let a := r-σ^2/2
    let y := y0+a*t+σ*x
    barrierBrownianPrice b K r σ T y0 ![t,x]=Real.exp (-r*T)*
      (barrierGaussianAverage b K a σ (T-t) y-
        Real.exp (-(2*r/σ^2-1)*y)*barrierGaussianAverage b K a σ (T-t) (-y)) := by
  dsimp only
  let a := r-σ^2/2
  let y := y0+a*t+σ*x
  have hv : 0<σ^2*(T-t) := by positivity
  have hν : (2*r/σ^2-1)*(σ^2*(T-t))=2*a*(T-t) := by
    have hh := barrier_reflection_parameter r σ hσ.ne'
    dsimp [a]
    linear_combination (T-t)*hh
  have he := image_heat_gaussian_formula (barrierLogPayoff b K) a (T-t) (2*r/σ^2-1) y (σ^2*(T-t)) hv hν
  rw [barrier_gaussian_average_pdf b K a σ (T-t) y hσ (sub_pos.mpr ht),
    barrier_gaussian_average_pdf b K a σ (T-t) (-y) hσ (sub_pos.mpr ht)] at he
  dsimp only [barrierBrownianPrice,brownianHeatPrice,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [show y0+(r-σ^2/2)*T+σ*x=y+a*(T-t) by dsimp [y,a];ring,he]

/-- The image price vanishes on the moving Brownian-coordinate barrier. -/
theorem barrier_brownian_boundary (b K r σ T y0 t x : ℝ) (hσ : 0<σ) (ht : t<T)
    (hy : y0+(r-σ^2/2)*t+σ*x=0) :
    barrierBrownianPrice b K r σ T y0 ![t,x]=0 := by
  rw [barrier_brownian_gaussian_formula b K r σ T y0 t x hσ ht]
  simp [hy]

/-- The actual discounted price converges along any continuous stock
path ending strictly below the barrier. -/
theorem barrier_brownian_moving_endpoint (b K r σ T y0 : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ)
    (W : ℝ → ℝ) (hW : ContinuousAt W T)
    (hy : y0+(r-σ^2/2)*T+σ*W T<0) :
    Tendsto (fun t => barrierBrownianPrice b K r σ T y0 ![t,W t]) (𝓝[<] T)
      (𝓝 (Real.exp (-r*T)*max (b*Real.exp (y0+(r-σ^2/2)*T+σ*W T)-K) 0)) := by
  let y := y0+(r-σ^2/2)*T+σ*W T
  have hg := barrier_image_joint_endpoint b K (r-σ^2/2) σ (2*r/σ^2-1) 0 y hb hK hKb hσ.le hy
  simp only [zero_mul,neg_zero,Real.exp_zero,one_mul] at hg
  have hmap : Tendsto (fun t => (T-t,y0+(r-σ^2/2)*t+σ*W t)) (𝓝[<] T) (𝓝 (0,y)) := by
    have ht : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) := nhdsWithin_le_nhds
    have hh := ((tendsto_const_nhds (x:=T)).sub ht).prodMk_nhds
      (((tendsto_const_nhds (x:=y0)).add ((tendsto_const_nhds (x:=r-σ^2/2)).mul ht)).add ((tendsto_const_nhds (x:=σ)).mul (hW.tendsto.mono_left nhdsWithin_le_nhds)))
    simpa only [sub_self] using hh
  have he := (hg.comp hmap).const_mul (Real.exp (-r*T))
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (barrier_brownian_gaussian_formula b K r σ T y0 t (W t) hσ ht).symm

end Asakura.Chapter11
