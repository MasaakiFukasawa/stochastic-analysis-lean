import Chapter12RapidDecayIntegrable
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

open MeasureTheory Filter
open scoped Topology CompactlySupported
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Adding an independent noise tending to zero gives the weak limit
used for Gaussian regularization. The argument uses only bounded tests
and dominated convergence, so it applies to every Gaussian variance sequence. -/
theorem small_noise_compact_test_limit {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ γ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (f : C_c(E, ℝ)) :
    Tendsto (fun n => ∫ x,f x ∂(μ.prod γ).map (fun z : E × E => z.1+ε n • z.2))
      atTop (𝓝 (∫ x,f x ∂μ)) := by
  let C := ‖f.toBoundedContinuousFunction‖
  have hbound (n) (z : E × E) : ‖f (z.1+ε n • z.2)‖≤C :=
    f.toBoundedContinuousFunction.norm_coe_le_norm _
  have hm (n) : Measurable (fun z : E × E => z.1+ε n • z.2) := by fun_prop
  have hlim (z : E × E) : Tendsto (fun n => f (z.1+ε n • z.2)) atTop (𝓝 (f z.1)) := by
    have ht := (tendsto_const_nhds (x := z.1) (f := atTop)).add (hε.smul_const z.2)
    have he : z.1+(0:ℝ) • z.2=z.1 := by simp
    rw [he] at ht
    exact f.continuous.continuousAt.tendsto.comp ht
  have ht := tendsto_integral_of_dominated_convergence (fun _ : E × E => C)
    (fun n => (f.continuous.measurable.comp (hm n)).aestronglyMeasurable)
    (integrable_const (μ := μ.prod γ) _) (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hlim)
  have hmap n : (∫ x,f x ∂(μ.prod γ).map (fun z : E × E => z.1+ε n • z.2))=
      ∫ z : E × E,f (z.1+ε n • z.2) ∂μ.prod γ :=
    integral_map (hm n).aemeasurable f.continuous.aestronglyMeasurable
  have hfst : (∫ z : E × E,f z.1 ∂μ.prod γ)=∫ x,f x ∂μ := by
    rw [integral_prod]
    · simp
    · exact (f.toBoundedContinuousFunction.integrable μ).comp_fst γ
  change Tendsto (fun n => ∫ z : E × E,f (z.1+ε n • z.2) ∂μ.prod γ) atTop
    (𝓝 (∫ z : E × E,f z.1 ∂μ.prod γ)) at ht
  simpa only [hmap,hfst] using ht

end Asakura.Chapter12
