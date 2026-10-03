import Chapter2ProgressiveEnergySpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The sigma algebra encoding all the finite-time progressive restrictions. -/
noncomputable def energyProgressiveSigma
    {Ω : Type*} (m : MeasurableSpace Ω) {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (c : ℕ → ℝ) : MeasurableSpace (Ω × ℝ) :=
  m.prod inferInstance ⊓ ⨅ n, MeasurableSpace.map
    (fun z : Ω × Icc (0:ℝ) (c n) => (z.1,z.2.val))
    (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val)))

theorem energy_progressive_measurable_iff
    {Ω : Type*} {m : MeasurableSpace Ω} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (c : ℕ → ℝ) (H : Ω × ℝ → ℝ) :
    @Measurable _ _ (energyProgressiveSigma m F c) inferInstance H ↔
      Measurable H ∧ (∀ n, @Measurable _ _
        (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val))) := by
  constructor
  · intro h
    refine ⟨h.mono inf_le_left le_rfl,?_⟩
    intro n s hs
    exact MeasurableSpace.measurableSet_iInf.mp (h hs).2 n
  · rintro ⟨h,hp⟩ s hs
    exact ⟨h hs,MeasurableSpace.measurableSet_iInf.mpr (fun n => hp n hs)⟩

/-- The actual progressive domain is a closed measurable L2 subspace. No
sigma-finiteness of the measure trimmed to the progressive sigma algebra is
assumed or needed. -/
theorem progressive_energy_range_eq_lpMeas
    {Ω : Type*} {m : MeasurableSpace Ω} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (c : ℕ → ℝ) (ν : Measure (Ω × ℝ)) :
    progressiveEnergyRange F c ν = lpMeas ℝ ℝ (energyProgressiveSigma m F c) 2 ν := by
  ext v
  constructor
  · rintro ⟨H,rfl⟩
    apply mem_lpMeas_iff_aestronglyMeasurable.mpr
    have hm := (energy_progressive_measurable_iff F c H.val).mpr ⟨H.property.1,H.property.2.1⟩
    exact hm.aestronglyMeasurable.congr H.property.2.2.coeFn_toLp.symm
  · intro hv
    have hm := mem_lpMeas_iff_aestronglyMeasurable.mp hv
    let H := hm.mk v
    have hH : @Measurable _ _ (energyProgressiveSigma m F c) inferInstance H := hm.stronglyMeasurable_mk.measurable
    have hi : MemLp H 2 ν := (Lp.memLp v).ae_eq hm.ae_eq_mk
    have hp := (energy_progressive_measurable_iff F c H).mp hH
    let G : progressiveEnergyIntegrands F c ν := ⟨H,hp.1,hp.2,hi⟩
    refine ⟨G,?_⟩
    apply Lp.ext
    exact hi.coeFn_toLp.trans hm.ae_eq_mk.symm

theorem progressive_energy_complete
    {Ω : Type*} {m : MeasurableSpace Ω} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (c : ℕ → ℝ) (ν : Measure (Ω × ℝ)) :
    CompleteSpace (progressiveEnergyRange F c ν) := by
  rw [progressive_energy_range_eq_lpMeas]
  letI : Fact (energyProgressiveSigma m F c ≤ m.prod inferInstance) := ⟨inf_le_left⟩
  infer_instance

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.progressive_energy_range_eq_lpMeas
#print axioms Asakura.Chapter2Complete.progressive_energy_complete
