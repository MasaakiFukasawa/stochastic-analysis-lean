import Chapter10LinearDriftContinuity

open MeasureTheory Set Filter
open scoped Topology BigOperators NNReal
namespace Asakura.Chapter10
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Differentiate the proved covariance integral equation, including its
right derivative at zero. No derivative of an expectation is assumed. -/
theorem linear_covariance_derivative {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (T : ℝ) (hT : 0≤T)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)) (hm : Measurable X) (hX : MemLp X 2 P)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K) (i j : Fin d)
    (q : ℝ → ℝ) (hq : Continuous q) (v₀ : ℝ)
    (he : ∀ r : Icc (0:ℝ) T,
      (∫ w,X w r i*X w r j ∂P)=v₀+
        (∫ s in 0..r.val,∫ w,X w (projIcc 0 T hT s) j*(A s (X w (projIcc 0 T hT s))) i ∂P)+
        (∫ s in 0..r.val,∫ w,X w (projIcc 0 T hT s) i*(A s (X w (projIcc 0 T hT s))) j ∂P)+
        (∫ s in 0..r.val,q s)) :
    ∀ t∈Ico 0 T,HasDerivWithinAt
      (fun s => ∫ w,X w (projIcc 0 T hT s) i*X w (projIcc 0 T hT s) j ∂P)
      ((∫ w,X w (projIcc 0 T hT t) j*(A t (X w (projIcc 0 T hT t))) i ∂P)+
        (∫ w,X w (projIcc 0 T hT t) i*(A t (X w (projIcc 0 T hT t))) j ∂P)+q t) (Ici t) t := by
  intro t ht
  let f := fun s => ∫ w,X w (projIcc 0 T hT s) j*(A s (X w (projIcc 0 T hT s))) i ∂P
  let g := fun s => ∫ w,X w (projIcc 0 T hT s) i*(A s (X w (projIcc 0 T hT s))) j ∂P
  have hf : Continuous f := linear_drift_moment_continuous P T hT X hm hX A hA K hAK i j
  have hg : Continuous g := linear_drift_moment_continuous P T hT X hm hX A hA K hAK j i
  have hdf := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hdg := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hdq := intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable 0 t)
    hq.stronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt
  have hd := ((hdf.const_add v₀).add hdg).add hdq
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
  · have hlt : ∀ᶠ s in 𝓝[Ici t] t,s<T := (eventually_lt_nhds ht.2).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hlt] with s hs hsT
    have hs' : s∈Icc (0:ℝ) T := ⟨ht.1.trans hs,hsT.le⟩
    have hp : projIcc 0 T hT s=⟨s,hs'⟩ := Subtype.ext (by simp [projIcc,hs'.1,hs'.2])
    simpa only [hp,Pi.add_apply,f,g] using he ⟨s,hs'⟩
  · exact (show t∈Ici t from le_refl t)

end Asakura.Chapter10
