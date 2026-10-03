import Chapter10CovarianceDerivative
import Chapter10CovarianceODEUniqueness

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- A centered initial value stays centered once the actual expectation equation
has been proved. The right derivative at zero is sufficient. -/
theorem homogeneous_mean_equation_zero {d : ℕ}
    (m : ℝ → Fin d → ℝ) (hm : Continuous m)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (T K : ℝ) (hT : 0≤T) (hAK : ∀ s∈Ico 0 T,‖A s‖≤K)
    (he : ∀ s∈Icc 0 T,∀ i,m s i=∫ t in 0..s,(A t (m t)) i) :
    ∀ s∈Icc 0 T,m s=0 := by
  have hc : Continuous (fun t => A t (m t)) := hA.clm_apply hm
  have hd : ∀ t∈Ico 0 T,HasDerivWithinAt m (A t (m t)) (Ici t) t := by
    intro t ht
    apply hasDerivWithinAt_pi.mpr
    intro i
    have hci := (continuous_apply i).comp hc
    have hi := intervalIntegral.integral_hasDerivAt_right (hci.intervalIntegrable 0 t)
      hci.stronglyMeasurable.stronglyMeasurableAtFilter hci.continuousAt
    apply hi.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · have hlt : ∀ᶠ s in 𝓝[Ici t] t,s<T := (eventually_lt_nhds ht.2).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin,hlt] with s hs hsT
      exact he s ⟨ht.1.trans hs,hsT.le⟩ i
    · exact le_refl t
  have h0 : m 0=0 := by
    ext i
    simpa only [intervalIntegral.integral_same,Pi.zero_apply] using he 0 ⟨le_rfl,hT⟩ i
  apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := m) (f' := fun t => A t (m t)) (K := K) hm.continuousOn hd h0
  intro t ht
  exact ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hAK t ht) (norm_nonneg _))

end Asakura.Chapter10
