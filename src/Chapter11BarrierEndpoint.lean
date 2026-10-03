import Chapter11HeatEndpoint
import Chapter11BarrierBounds

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace Asakura.Chapter11
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- A bounded Borel payoff needs continuity only at the limiting point,
not at the barrier corner. -/
theorem bounded_gaussian_endpoint (f : ℝ → ℝ) (hf : Measurable f)
    (K : ℝ) (hb : ∀ z,|f z|≤K) (y : ℝ) (hfy : ContinuousAt f y) :
    ContinuousAt (fun q : ℝ × ℝ => ∫ z,f (q.2+Real.sqrt q.1*z) ∂gaussianReal 0 1) (0,y) := by
  apply continuousAt_of_dominated (bound:=fun _ => K)
  · exact Eventually.of_forall fun q => (hf.comp (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall fun q => ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb _
  · exact integrable_const _
  · apply ae_of_all
    intro z
    exact hfy.comp_of_eq (show ContinuousAt (fun q : ℝ × ℝ => q.2+Real.sqrt q.1*z) (0,y) by fun_prop) (by simp)

theorem barrier_log_payoff_continuousAt (b K y : ℝ) (hy : y≠0) :
    ContinuousAt (fun z : ℝ => if z<0 then max (b*Real.exp z-K) 0 else 0) y := by
  rcases lt_or_gt_of_ne hy with hy|hy
  · apply ContinuousAt.congr_of_eventuallyEq (f:=fun z => max (b*Real.exp z-K) 0) (by fun_prop)
    filter_upwards [gt_mem_nhds hy] with z hz
    exact if_pos hz
  · apply ContinuousAt.congr_of_eventuallyEq (f:=fun _ : ℝ => (0:ℝ)) continuousAt_const
    filter_upwards [lt_mem_nhds hy] with z hz
    exact if_neg (not_lt_of_ge hz.le)

noncomputable def barrierGaussianAverage (b K a σ θ y : ℝ) : ℝ :=
  ∫ z,(if y+a*θ+σ*Real.sqrt θ*z<0 then max (b*Real.exp (y+a*θ+σ*Real.sqrt θ*z)-K) 0 else 0) ∂gaussianReal 0 1

/-- Joint endpoint convergence supplies the actual moving-path limit
needed after stopping, not merely convergence for a fixed stock price. -/
theorem barrier_gaussian_joint_endpoint (b K a σ y : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0≤σ) (hy : y≠0) :
    ContinuousAt (fun q : ℝ × ℝ => barrierGaussianAverage b K a σ q.1 q.2) (0,y) := by
  let f := fun z : ℝ => if z<0 then max (b*Real.exp z-K) 0 else 0
  obtain ⟨hm,hn,hbound,_⟩ := barrier_log_payoff_bounds b K hb hK hKb
  have hf := bounded_gaussian_endpoint f hm (b-K) (fun z => by rw [abs_of_nonneg (hn z)];exact hbound z)
    y (barrier_log_payoff_continuousAt b K y hy)
  have hc : ContinuousAt (fun q : ℝ × ℝ => (σ^2*q.1,q.2+a*q.1)) (0,y) := by fun_prop
  have hh := hf.comp_of_eq hc (by simp)
  convert hh using 1
  funext q
  dsimp only [Function.comp_def,barrierGaussianAverage,f]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  rw [Real.sqrt_mul (sq_nonneg σ),Real.sqrt_sq_eq_abs,abs_of_nonneg hσ]

/-- The reflected endpoint is zero inside the barrier, so the image
solution has precisely the required terminal payoff. -/
theorem barrier_image_joint_endpoint (b K a σ ν r y : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0≤σ) (hy : y<0) :
    Tendsto (fun q : ℝ × ℝ => Real.exp (-r*q.1)*
      (barrierGaussianAverage b K a σ q.1 q.2-
        Real.exp (-ν*q.2)*barrierGaussianAverage b K a σ q.1 (-q.2)))
      (𝓝 (0,y)) (𝓝 (max (b*Real.exp y-K) 0)) := by
  have hf := barrier_gaussian_joint_endpoint b K a σ y hb hK hKb hσ hy.ne
  have hg := barrier_gaussian_joint_endpoint b K a σ (-y) hb hK hKb hσ (neg_ne_zero.mpr hy.ne)
  have hneg : ContinuousAt (fun q : ℝ × ℝ => (q.1,-q.2)) (0,y) := by fun_prop
  have hg' := hg.comp_of_eq hneg (by simp)
  have he : ContinuousAt (fun q : ℝ × ℝ => Real.exp (-ν*q.2)) (0,y) := by fun_prop
  have hd : ContinuousAt (fun q : ℝ × ℝ => Real.exp (-r*q.1)) (0,y) := by fun_prop
  have hh := hd.mul (hf.sub (he.mul hg'))
  change ContinuousAt (fun q : ℝ × ℝ => Real.exp (-r*q.1)*(barrierGaussianAverage b K a σ q.1 q.2-Real.exp (-ν*q.2)*barrierGaussianAverage b K a σ q.1 (-q.2))) (0,y) at hh
  simpa [ContinuousAt,barrierGaussianAverage,hy,show ¬ -y<0 by linarith] using hh

end Asakura.Chapter11
