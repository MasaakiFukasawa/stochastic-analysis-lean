import Chapter9FiniteIntervalMartingale

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The compensated test process has continuous paths and a deterministic
 uniform bound on each finite strip, so optional stopping applies in M₂. -/
theorem bounded_compensated_process {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ r,F r≤m)
    (U a : ℝ → Ω → ℝ) (b : ℝ) (hb : 0≤b)
    (hU : ∀ r∈Icc 0 b,Measurable[F r] (U r))
    (hUc : ∀ w,ContinuousOn (fun r => U r w) (Icc 0 b))
    (D : ℝ) (hUb : ∀ r∈Icc 0 b,∀ w,‖U r w‖≤D)
    (ha : ∀ r∈Icc 0 b,Measurable[F r] (a r))
    (hac : ∀ w,ContinuousOn (fun r => a r w) (Icc 0 b))
    (ham : Measurable (fun z : ℝ × Ω => a z.1 z.2))
    (C : ℝ) (hC : 0≤C) (hbound : ∀ r∈Icc 0 b,∀ w,‖a r w‖≤C)
    (hinc : ∀ s t,0≤s → s<t → t≤b →
      P[(fun w => U t w-∫ h,a (s+h) w ∂volume.restrict (Ioc 0 (t-s)))|F s]=ᵐ[P] U s) :
    (fun (t : HalfClosedTime) w =>
      U (finitePrefixTime b hb t).val w-U 0 w-
        ∫ r in 0..(finitePrefixTime b hb t).val,a r w) ∈
      boundedMProcess P (fun t => F (finitePrefixTime b hb t).val) := by
  letI : MeasurableSpace Ω := m
  have hUi r (hr : r∈Icc 0 b) : Integrable (U r) P :=
    Integrable.of_bound ((hU r hr).mono (hle r) le_rfl).aestronglyMeasurable D
      (ae_of_all _ (hUb r hr))
  apply finite_interval_bounded_martingale P F hle (fun t w => U t w-U 0 w-∫ r in 0..t,a r w) b hb (C := 2*D+b*C)
  · intro r hr
    apply Measurable.sub
    · exact (hU r hr).sub ((hU 0 ⟨le_rfl,hb⟩).mono (hF hr.1) le_rfl)
    · exact measurable_past_integral (m := F r) a r hr.1
        (fun u hu => (ha u ⟨hu.1,hu.2.trans hr.2⟩).mono (hF hu.2) le_rfl)
        (fun w => (hac w).mono (Icc_subset_Icc le_rfl hr.2))
  · intro w
    apply ((hUc w).sub continuousOn_const).sub
    have hi : IntervalIntegrable (fun r => a r w) volume 0 b := (hac w).intervalIntegrable_of_Icc hb
    simpa only [uIcc_of_le hb] using intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  · intro r hr w
    have hi : ‖∫ u in 0..r,a u w‖≤r*C := by
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := r) (C := C) (f := fun u => a u w)
        (fun u hu => hbound u ⟨(uIoc_of_le hr.1 ▸ hu).1.le,(uIoc_of_le hr.1 ▸ hu).2.trans hr.2⟩ w)
      simpa only [sub_zero,abs_of_nonneg hr.1,mul_comm] using hh
    have hh := (norm_sub_le (U r w-U 0 w) (∫ u in 0..r,a u w)).trans
      (add_le_add (norm_sub_le (U r w) (U 0 w)) hi)
    nlinarith [hUb r hr w,hUb 0 ⟨le_rfl,hb⟩ w,mul_le_mul_of_nonneg_right hr.2 hC]
  · exact compensated_process_martingale P F hF hle U a b hb hU hUi ha hac ham C hbound hinc
  · intro w
    simp
end Asakura.Chapter9
