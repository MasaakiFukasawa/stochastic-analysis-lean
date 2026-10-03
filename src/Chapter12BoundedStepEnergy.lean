import Chapter12DeterministicEnergy
import Chapter12FiniteWienerIndicator
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The bounded past coefficient times an interval indicator belongs to the
concrete progressive energy space of the chapter-5 Ito isometry. -/
noncomputable def boundedStepEnergy {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t,F t ≤ ‹MeasurableSpace Ω›) (c : ℕ → ℝ)
    (a b : ℝ) (G : Ω → ℝ) (hGm : Measurable[F (realTimeClamp a)] G) (hG : MemLp G ∞ P) :
    progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi (0:ℝ)))) := by
  let H : Ω × ℝ → ℝ := fun z => (Ioc a b).indicator (fun _ => G z.1) z.2
  have hm : Measurable H := by
    have hg : Measurable (fun z : Ω × ℝ => G z.1) := (hGm.mono (hle _) le_rfl).comp measurable_fst
    exact hg.indicator (measurableSet_Ioc.preimage measurable_snd)
  have hp n : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)) := by
    apply (measurable_progressive_iff _ _).mpr
    intro u
    letI : MeasurableSpace Ω := F (realTimeClamp u.val)
    by_cases hau : a ≤ u.val
    · have hgu : Measurable G := hGm.mono (hF (real_time_clamp_mono hau)) le_rfl
      exact (hgu.comp measurable_fst).indicator (measurableSet_Ioc.preimage
        (measurable_subtype_coe.comp (measurable_subtype_coe.comp measurable_snd)))
    · have he : (fun z : Ω × Iic u => H (z.1,z.2.val.val)) = 0 := by
        funext z
        have hh : z.2.val.val ∉ Ioc a b := by
          intro hz
          exact hau (hz.1.le.trans z.2.property)
        simp [H,hh]
      rw [he]
      exact measurable_const
  have ht : Integrable ((Ioc a b).indicator (fun _ => (1:ℝ))) (volume.restrict (Ioi (0:ℝ))) := by
    exact memLp_one_iff_integrable.mp (memLp_indicator_const 1 measurableSet_Ioc (1:ℝ)
      (Or.inr (half_line_interval_measure_ne_top a b)))
  have hprod := (hG.mono_exponent (show (2:ℝ≥0∞) ≤ ∞ from le_top)).integrable_sq.mul_prod ht
  have hi : MemLp H 2 (P.prod (volume.restrict (Ioi (0:ℝ)))) := by
    apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
    apply hprod.congr
    exact ae_of_all _ (fun z => by by_cases hz : z.2 ∈ Ioc a b <;> simp [H,hz])
  exact ⟨H,hm,hp,hi⟩

end Asakura.Chapter12
