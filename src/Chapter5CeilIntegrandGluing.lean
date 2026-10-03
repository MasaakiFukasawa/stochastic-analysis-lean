import Chapter5CountableIntegrandGluing

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The specific ceiling-index pasting printed in the martingale
representation proof is progressive on every finite interval. -/
theorem ceil_integrand_progressive
    {Ω : Type*} (R : ℝ) (F : Icc (0:ℝ) R → MeasurableSpace Ω)
    (H : ℕ → Ω × ℝ → ℝ)
    (hH : ∀ n,@Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H n (z.1,z.2.val))) :
    @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H (Nat.ceil z.2.val) (z.1,z.2.val)) :=
  progressive_countable_time_choice F (fun t => Nat.ceil t.val)
    (Nat.measurable_ceil.comp measurable_subtype_coe) _ hH

/-- Global L² integrability of each separate increment yields L²
integrability of the pasted integrand on every finite interval. -/
theorem ceil_integrand_local_L2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω × ℝ → ℝ) (hm : ∀ n,Measurable (H n))
    (hi : ∀ n,MemLp (H n) 2 (P.prod (volume.restrict (Ioi (0:ℝ))))) (R : ℝ) :
    MemLp (fun z => H (Nat.ceil z.2) z) 2 (P.prod (volume.restrict (Ioc 0 R))) := by
  refine finite_choice_memLp_two (P.prod (volume.restrict (Ioc (0:ℝ) R))) (fun z => Nat.ceil z.2)
    (Nat.measurable_ceil.comp measurable_snd) (Nat.ceil R) ?_ H hm ?_
  · have hs : MeasurableSet {z : Ω × ℝ | Nat.ceil z.2 ≤ Nat.ceil R} :=
      measurableSet_le (Nat.measurable_ceil.comp measurable_snd) measurable_const
    apply (Measure.ae_prod_iff_ae_ae hs).mpr
    apply ae_of_all
    intro w
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Nat.ceil_mono hr.2
  · intro n _
    exact (hi n).mono_measure (Measure.prod_mono (le_refl P)
      (Measure.restrict_mono (show Ioc (0:ℝ) R ⊆ Ioi 0 from fun r hr => hr.1) (le_refl volume)))

end Asakura.Chapter5
