import Chapter8GeneratorExpectationContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.TangentCone.Real

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

/-- The integral form of Dynkin's formula gives the right generator at
zero once the expected generator value is continuous. -/
theorem right_generator_from_integral (u v : ℝ → ℝ) (hc : Continuous v)
    (T : ℝ) (hT : 0<T)
    (hu : ∀ t,t∈Icc 0 T → u t=u 0+∫ s in 0..t,v s) :
    HasDerivWithinAt u (v 0) (Ici 0) 0 := by
  have hd : HasDerivAt (fun t => u 0+∫ s in 0..t,v s) (v 0) 0 := by
    exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
  · have ht : ∀ᶠ t in 𝓝[Ici (0:ℝ)] 0,t<T :=
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,ht] with t ht0 htT
    exact hu t ⟨ht0,htT.le⟩
  · exact (show (0:ℝ)∈Ici 0 from le_refl (0:ℝ))

/-- Semigroup composition identifies the right generator applied to
P_t f with its time derivative. This is the equality L P_t f=P_t L f
used in the Gibbs proof; it is not assumed as a commutation rule. -/
theorem semigroup_backward_generator {E : Type*}
    (P : ℝ → (E → ℝ) → E → ℝ) (G : ℝ → E → ℝ) (L : (E → ℝ) → E → ℝ)
    (t : ℝ) (x : E) (v : ℝ)
    (htime : HasDerivAt (fun s => G s x) v t)
    (hzero : HasDerivWithinAt (fun h => P h (G t) x) (L (G t) x) (Ici 0) 0)
    (hsemi : ∀ h,0 ≤ h → P h (G t) x=G (t+h) x) :
    L (G t) x=v := by
  have hd : HasDerivAt (fun h => G (t+h) x) v 0 := by
    have ht' : HasDerivAt (fun s => G s x) v (t+0) := by simpa only [add_zero] using htime
    simpa only [Function.comp_def,id_eq,mul_one] using ht'.comp 0 ((hasDerivAt_id (0:ℝ)).const_add t)
  have hright : HasDerivWithinAt (fun h => G (t+h) x) (L (G t) x) (Ici 0) 0 :=
    hzero.congr_of_mem (fun h hh => (hsemi h hh).symm) (show (0:ℝ)∈Ici 0 from le_refl (0:ℝ))
  exact (hright.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0))

end Asakura.Chapter8
