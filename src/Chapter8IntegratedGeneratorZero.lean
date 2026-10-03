import Chapter8SemigroupGenerator
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Once the actual backward equation and the integrated generator
identity are available, differentiation under the initial distribution
proves that its propagated smooth-test integrals remain constant. -/
theorem integrated_generator_zero_constant {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π]
    (G H : ℝ → E → ℝ) (T M C : ℝ) (hT : 0 ≤ T)
    (R : E → ℝ) (hR : Integrable R π)
    (hGm : ∀ t,t∈Icc 0 T → AEStronglyMeasurable (G t) π)
    (hGb : ∀ t,t∈Icc 0 T → ∀ᵐ x ∂π,‖G t x‖ ≤ M)
    (hGc : ∀ᵐ x ∂π,ContinuousOn (fun t => G t x) (Icc 0 T))
    (hHm : ∀ t,t∈Ioo 0 T → AEStronglyMeasurable (H t) π)
    (hHb : ∀ᵐ x ∂π,∀ t,t∈Ioo 0 T → ‖H t x‖ ≤ C*(1+R x))
    (hder : ∀ᵐ x ∂π,∀ t,t∈Ioo 0 T → HasDerivAt (fun s => G s x) (H t x) t)
    (hzero : ∀ t,t∈Ioo 0 T → ∫ x,H t x ∂π=0) :
    (∫ x,G T x ∂π)=∫ x,G 0 x ∂π := by
  let u := fun t => ∫ x,G t x ∂π
  have hc : ContinuousOn u (Icc 0 T) :=
    continuousOn_of_dominated hGm hGb (integrable_const M) hGc
  have hd t (ht : t∈Ioo 0 T) : HasDerivAt u 0 t := by
    have hmeas : ∀ᶠ s in 𝓝 t,AEStronglyMeasurable (G s) π := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hGm s ⟨hs.1.le,hs.2.le⟩
    have hi : Integrable (G t) π := Integrable.mono' (integrable_const M)
      (hGm t ⟨ht.1.le,ht.2.le⟩) (hGb t ⟨ht.1.le,ht.2.le⟩)
    have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioo_mem_nhds ht.1 ht.2)
      hmeas hi (hHm t ht) hHb (((integrable_const (1:ℝ)).add hR).const_mul C) hder
    simpa only [hzero t ht] using hh.2
  have hmono : MonotoneOn u (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hc
    · intro t ht
      exact (hd t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (by simpa only [interior_Icc] using ht)).deriv]
  have hanti : AntitoneOn u (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hc
    · intro t ht
      exact (hd t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (by simpa only [interior_Icc] using ht)).deriv]
  exact le_antisymm (hanti ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT)
    (hmono ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT)

end Asakura.Chapter8
