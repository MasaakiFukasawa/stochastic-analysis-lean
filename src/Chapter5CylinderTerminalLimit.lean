import Chapter5VectorHeatEndpoint

open MeasureTheory Set Filter
open scoped Topology NNReal BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 1800000

/-- Joint terminal convergence of a vector Gaussian average, including
moving random spatial parameters after fixing a sample point. -/
theorem vector_heat_endpoint_limit
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsProbabilityMeasure ν] (hi : Integrable (fun z : E => z) ν)
    (l : Filter ι) (f : E → ℝ) (C : ℝ≥0) (hf : LipschitzWith C f)
    (x : E) (xs : ι → E) (ts : ι → ℝ)
    (hx : Tendsto xs l (𝓝 x)) (ht : Tendsto ts l (𝓝 0)) :
    Tendsto (fun n => ∫ z,f (xs n+Real.sqrt (ts n) • z) ∂ν) l (𝓝 (f x)) := by
  have h1 : Tendsto (fun n => ‖xs n-x‖) l (𝓝 0) := by
    simpa using (hx.sub_const x).norm
  have h2 : Tendsto (fun n => Real.sqrt (ts n)) l (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp ht
  have hb : Tendsto (fun n => (C:ℝ)*(‖xs n-x‖+Real.sqrt (ts n)*(∫ z,‖z‖ ∂ν))) l (𝓝 0) := by
    simpa using (h1.add (h2.mul_const (∫ z,‖z‖ ∂ν))).const_mul (C:ℝ)
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.dist_eq] using squeeze_zero
    (fun n => abs_nonneg ((∫ z,f (xs n+Real.sqrt (ts n) • z) ∂ν)-f x))
    (fun n => vector_heat_endpoint_bound ν hi f C hf (xs n) x (ts n)) hb

/-- Countably many preterminal identities suffice: a common null set is
obtained before passing to the actual terminal values of the processes. -/
theorem cylinder_representation_terminal_limit
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (ν : Measure E) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : E => z) ν)
    (f : E → ℝ) (C : ℝ≥0) (hf : LipschitzWith C f)
    {d : ℕ} (X : ℕ → Ω → E) (XT : Ω → E) (ts : ℕ → ℝ)
    (A : Ω → ℝ) (M : Fin d → ℕ → Ω → ℝ) (MT : Fin d → Ω → ℝ)
    (hx : ∀ᵐ w ∂P,Tendsto (fun n => X n w) atTop (𝓝 (XT w)))
    (ht : Tendsto ts atTop (𝓝 0))
    (hm : ∀ i,∀ᵐ w ∂P,Tendsto (fun n => M i n w) atTop (𝓝 (MT i w)))
    (he : ∀ n,(fun w => ∫ z,f (X n w+Real.sqrt (ts n) • z) ∂ν) =ᵐ[P]
      fun w => A w+∑ i,M i n w) :
    (fun w => f (XT w)) =ᵐ[P] fun w => A w+∑ i,MT i w := by
  filter_upwards [hx,ae_all_iff.mpr hm,ae_all_iff.mpr he] with w hxw hmw hew
  have hleft := vector_heat_endpoint_limit ν hi atTop f C hf (XT w) (fun n => X n w) ts hxw ht
  have hright := (tendsto_const_nhds (x := A w)).add (tendsto_finsetSum Finset.univ (fun i _ => hmw i))
  exact tendsto_nhds_unique hleft (hright.congr (fun n => (hew n).symm))

end Asakura.Chapter5
