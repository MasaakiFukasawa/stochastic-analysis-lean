import Chapter9GaussianSmoothness

open MeasureTheory Filter Set
open scoped Topology
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The lower-endpoint limit after the manuscript's Gaussian change of
variables. The proof is actual dominated convergence; the test family may
depend on time, as f(y) p_(tau-h)(y) does in the reverse transition. -/
theorem reverse_gaussian_approximation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (q : ℝ → E → ℝ) (x : E) (d : ℕ) (δ : ℝ) (hδ : 0<δ)
    (hq : ContinuousAt (Function.uncurry q) (0,x))
    (hqm : ∀ h∈Ioo 0 δ,AEStronglyMeasurable
      (fun ξ => q h (Real.exp h • (x-Real.sqrt (1-Real.exp (-2*h)) • ξ))) P)
    (M : ℝ) (hM : ∀ h∈Ioo 0 δ,∀ y,‖q h y‖≤M) :
    Tendsto (fun h => Real.exp ((d:ℝ)*h)*
      (∫ ξ,q h (Real.exp h • (x-Real.sqrt (1-Real.exp (-2*h)) • ξ)) ∂P))
      (𝓝[>] (0:ℝ)) (𝓝 (q 0 x)) := by
  have hsmall : ∀ᶠ h in 𝓝[>] (0:ℝ),h∈Ioo 0 δ := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),h<δ from
        nhdsWithin_le_nhds (Iio_mem_nhds hδ))] with h hh hhδ
    exact ⟨hh,hhδ⟩
  have ht : Tendsto (fun h => ∫ ξ,q h (Real.exp h • (x-Real.sqrt (1-Real.exp (-2*h)) • ξ)) ∂P)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ _ : E,q 0 x ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    · exact hsmall.mono (fun h hh => hqm h hh)
    · exact hsmall.mono (fun h hh => ae_of_all _ (fun ξ => hM h hh _))
    · exact integrable_const _
    · apply ae_of_all
      intro ξ
      have hc : Continuous (fun h : ℝ => (h,Real.exp h • (x-Real.sqrt (1-Real.exp (-2*h)) • ξ))) := by
        fun_prop
      have hc0 : Tendsto (fun h : ℝ => (h,Real.exp h • (x-Real.sqrt (1-Real.exp (-2*h)) • ξ)))
          (𝓝[>] (0:ℝ)) (𝓝 (0,x)) := by
        simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
      exact hq.tendsto.comp hc0
  have he : Tendsto (fun h : ℝ => Real.exp ((d:ℝ)*h)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    simpa using ((show Continuous (fun h : ℝ => Real.exp ((d:ℝ)*h)) by fun_prop).continuousAt
      (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  simpa using he.mul ht
end Asakura.Chapter9
