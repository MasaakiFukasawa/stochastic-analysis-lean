import Chapter9CompactMixtureContinuity
import Chapter9UniformScoreBound
import Chapter8ForcedIntegralExistence
import Chapter9TimeDependentStability

open MeasureTheory Set Filter
open scoped NNReal Topology
namespace Asakura.Chapter9
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable def ouProbabilityVelocity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] (μ : Measure E) (d : ℕ)
    (t : ℝ) (y : E) : E :=
  let c := Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*(1-Real.exp (-2*t))))
  let a := Real.exp (-t)
  let v := 1-Real.exp (-2*t);
  -y-(∫ x,radialKernel c a v x y ∂μ)⁻¹ •
    (∫ x,(-radialKernel c a v x y/v) • (y-a • x) ∂μ)

/-- The actual velocity, extended below epsilon, is jointly continuous and
has a single global spatial Lipschitz constant for all extended times. -/
theorem ou_clamped_velocity_regularity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [ProperSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (d : ℕ)
    (R : ℝ) (hR : 0≤R) (hb : ∀ᵐ x ∂μ,‖x‖≤R)
    (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ≥0, Continuous (fun z : ℝ × E => ouProbabilityVelocity μ d (ε+max z.1 0) z.2) ∧
      ∀ s,LipschitzWith K (ouProbabilityVelocity μ d (ε+max s 0)) := by
  let τ := fun s : ℝ => ε+max s 0
  have hτ : Continuous τ := by dsimp [τ]; fun_prop
  have hτε s : ε≤τ s := by dsimp [τ]; linarith [le_max_right s (0:ℝ)]
  have hτp s : 0<τ s := hε.trans_le (hτε s)
  let v := fun s => 1-Real.exp (-2*τ s)
  let a := fun s => Real.exp (-τ s)
  let c := fun s => Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*v s))
  have hvp s : 0<v s := ou_variance_positive _ (hτp s)
  have hv : Continuous v := by dsimp [v]; fun_prop
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hc : Continuous c := by
    dsimp [c]
    fun_prop (disch := intro s; exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (hvp _).ne')
  let F := fun s y => ouProbabilityVelocity μ d (τ s) y
  have hFc : Continuous F.uncurry := by
    exact continuous_snd.neg.sub
      (compact_radial_score_continuous μ R hb c a v hc ha hv (fun _ => Real.exp_pos _) hvp)
  let w := 1-Real.exp (-2*ε)
  have hw : 0<w := ou_variance_positive _ hε
  let K : ℝ≥0 := ⟨1+1/w+R^2/w^2,by positivity⟩
  have hFK s : LipschitzWith K (F s) := by
    have hh := ou_strip_parameters ε (τ s) hε (hτε s)
    exact radial_velocity_uniform_lipschitz μ (c s) (a s) (v s) w R
      (Real.exp_pos _) hw hh.2.1 hh.2.2 hR hb
  exact ⟨K,hFc,hFK⟩

/-- Construct a solution on the whole finite positive-time strip from the
actual Gaussian-mixture velocity. The coefficient is extended below epsilon
only to apply the already proved global Volterra fixed-point construction. -/
theorem probability_flow_exists {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [ProperSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (d : ℕ)
    (R : ℝ) (hR : 0≤R) (hb : ∀ᵐ x ∂μ,‖x‖≤R)
    (ε H : ℝ) (hε : 0<ε) (hH : 0≤H) (x : E) :
    ∃ X : ℝ → E, Continuous X ∧
      (∀ s∈Icc 0 H,X s=x+∫ r in 0..s,ouProbabilityVelocity μ d (ε+r) (X r)) ∧
      ∀ s∈Ioo 0 H,HasDerivAt X (ouProbabilityVelocity μ d (ε+s) (X s)) s := by
  let τ := fun s : ℝ => ε+max s 0
  let F := fun s y => ouProbabilityVelocity μ d (τ s) y
  obtain ⟨K,hFc,hFK⟩ := ou_clamped_velocity_regularity μ d R hR hb ε hε
  obtain ⟨X,hXc,hX⟩ := Asakura.Chapter8.forced_integral_equation_exists H hH K F hFc hFK
    (fun _ => x) continuous_const
  have hFX : Continuous (fun s => F s (X s)) := hFc.comp (continuous_id.prodMk hXc)
  have he s (hs : 0≤s) : F s (X s)=ouProbabilityVelocity μ d (ε+s) (X s) := by
    dsimp [F,τ]
    rw [max_eq_left hs]
  refine ⟨X,hXc,?_,?_⟩
  · intro s hs
    rw [hX s hs]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    exact he r ((uIcc_of_le hs.1 ▸ hr).1)
  · intro s hs
    have hd := (intervalIntegral.integral_hasDerivAt_right
      (hFX.intervalIntegrable 0 s) hFX.aestronglyMeasurable.stronglyMeasurableAtFilter hFX.continuousAt).const_add x
    have heq : X =ᶠ[𝓝 s] (fun r => x+∫ u in 0..r,F u (X u)) := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
      exact hX r hr
    have hh := hd.congr_of_eventuallyEq heq
    simpa only [he s hs.1.le] using hh
end Asakura.Chapter9
