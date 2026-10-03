import Chapter8AveragedHessian

open MeasureTheory Set
namespace Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false

/-- Cancellation of common noise directly in two integral equations. -/
theorem common_noise_integral_difference {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (X Y W f g : ℝ → E) (x y : E) (T : ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hX : ∀ t ∈ Icc 0 T, X t = x+(∫ s in (0:ℝ)..t,f s)+W t)
    (hY : ∀ t ∈ Icc 0 T, Y t = y+(∫ s in (0:ℝ)..t,g s)+W t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => X s-Y s) (f t-g t) t := by
  have hdf := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable (μ := volume) 0 t)
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hdg := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable (μ := volume) 0 t)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hh : HasDerivAt (fun u => (x+∫ s in (0:ℝ)..u,f s)-(y+∫ s in (0:ℝ)..u,g s))
      (f t-g t) t := by
    convert (hdf.const_add x).sub (hdg.const_add y) using 1
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  rw [hX s ⟨hs.1.le,hs.2.le⟩,hY s ⟨hs.1.le,hs.2.le⟩]
  abel

end Asakura.Chapter8
