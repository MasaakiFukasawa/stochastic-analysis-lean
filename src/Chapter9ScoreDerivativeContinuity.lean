import Chapter9CompactMixtureContinuity

open MeasureTheory
namespace Asakura.Chapter9
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem continuous_rank_one {X E V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : X → E →L[ℝ] ℝ) (g : X → V) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (f x).smulRight (g x)) :=
  ((ContinuousLinearMap.smulRightL ℝ E V).continuous.comp hf).clm_apply hg

/-- Joint continuity of the actual spatial derivative of the score.
Time parameters need only be continuous, so the positive-time extension
used for the ODE is permitted. -/
theorem compact_radial_score_derivative_continuous {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [ProperSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (R : ℝ) (hb : ∀ᵐ x ∂μ,‖x‖≤R)
    (c a v : ℝ → ℝ) (hc : Continuous c) (ha : Continuous a) (hv : Continuous v)
    (hcp : ∀ t,0<c t) (hvp : ∀ t,0<v t) :
    Continuous (fun z : ℝ × E => fderiv ℝ (fun y =>
      (∫ x,radialKernel (c z.1) (a z.1) (v z.1) x y ∂μ)⁻¹ •
      (∫ x,(-radialKernel (c z.1) (a z.1) (v z.1) x y/v z.1) •
        (y-a z.1 • x) ∂μ)) z.2) := by
  let k := fun (z : ℝ × E) x => radialKernel (c z.1) (a z.1) (v z.1) x z.2
  let u := fun (z : ℝ × E) x => z.2-a z.1 • x
  have hb' : ∀ᵐ x ∂μ,x∈Metric.closedBall (0:E) R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hb
  have hk : Continuous k.uncurry := by
    dsimp [k,radialKernel]
    fun_prop (disch := intro w; exact mul_ne_zero (by norm_num) (hvp _).ne')
  have hu : Continuous u.uncurry := by dsimp [u]; fun_prop
  have hi : Continuous (fun w : (ℝ × E) × E => innerSL ℝ (u w.1 w.2)) :=
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous.comp hu
  have hkg : Continuous (fun w : (ℝ × E) × E => -k w.1 w.2/v w.1.1) := by
    fun_prop (disch := intro w; exact (hvp _).ne')
  have hkh : Continuous (fun w : (ℝ × E) × E => k w.1 w.2/(v w.1.1)^2) := by
    fun_prop (disch := intro w; exact pow_ne_zero 2 (hvp _).ne')
  have hp := compact_prior_integral_continuous μ _ (isCompact_closedBall 0 R) hb' k hk
  have hg := compact_prior_integral_continuous μ _ (isCompact_closedBall 0 R) hb'
    (fun z x => (-k z x/v z.1) • u z x) (hkg.smul hu)
  have hD := compact_prior_integral_continuous μ _ (isCompact_closedBall 0 R) hb'
    (fun z x => (-k z x/v z.1) • innerSL ℝ (u z x)) (hkg.smul hi)
  have hH := compact_prior_integral_continuous μ _ (isCompact_closedBall 0 R) hb'
    (fun z x => (-k z x/v z.1) • ContinuousLinearMap.id ℝ E+
      ((k z x/(v z.1)^2) • innerSL ℝ (u z x)).smulRight (u z x))
    ((hkg.smul continuous_const).add (continuous_rank_one _ _ (hkh.smul hi) hu))
  have hp0 z : (∫ x,k z x ∂μ)≠0 := (radial_mixture_positive μ _ _ _ (hcp _) (hvp _) z.2).ne'
  have he (z : ℝ × E) := (radial_score_fderiv μ (c z.1) (a z.1) (v z.1) (hcp _) (hvp _) z.2).fderiv
  simp_rw [he]
  exact ((hp.inv₀ hp0).smul hH).add (continuous_rank_one _ _
    (((hp.pow 2).inv₀ (fun z => pow_ne_zero 2 (hp0 z))).neg.smul hD) hg)
end Asakura.Chapter9
