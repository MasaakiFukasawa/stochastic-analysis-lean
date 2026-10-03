import Chapter8DynkinFubini

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8

/-- Dynkin's formula on a finite interval gives the time derivative in
its interior. Only continuity on that interval is required. -/
theorem dynkin_time_derivative (u v : ℝ → ℝ) (T : ℝ)
    (hc : ContinuousOn v (Icc 0 T))
    (hu : ∀ t,t∈Icc 0 T → u t=u 0+∫ s in 0..t,v s)
    (t : ℝ) (ht : t∈Ioo 0 T) : HasDerivAt u (v t) t := by
  have hc' : ContinuousOn v (Ioo 0 T) := hc.mono Ioo_subset_Icc_self
  have hi : IntervalIntegrable v volume 0 t :=
    (hc.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  have hd := (intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hc' t ht)
    (hc'.continuousAt (Ioo_mem_nhds ht.1 ht.2))).const_add (u 0)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact hu s ⟨hs.1.le,hs.2.le⟩

/-- At zero the same finite-interval argument gives the right derivative. -/
theorem dynkin_right_derivative (u v : ℝ → ℝ) (T : ℝ) (hT : 0<T)
    (hc : ContinuousOn v (Icc 0 T))
    (hu : ∀ t,t∈Icc 0 T → u t=u 0+∫ s in 0..t,v s) :
    HasDerivWithinAt u (v 0) (Ici 0) 0 := by
  let w := fun s => v (projIcc 0 T hT.le s)
  have hw : Continuous w :=
    (continuousOn_iff_continuous_restrict.mp hc).comp continuous_projIcc
  have hw0 : w 0 = v 0 := by simp only [w,projIcc_of_mem hT.le ⟨le_rfl,hT.le⟩]
  rw [← hw0]
  apply right_generator_from_integral u w hw T hT
  intro t ht
  rw [hu t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s∈Icc 0 T := (Icc_subset_Icc le_rfl ht.2) (by simpa only [uIcc_of_le ht.1] using hs)
  simp only [w,projIcc_of_mem hT.le hs']

end Asakura.Chapter8
