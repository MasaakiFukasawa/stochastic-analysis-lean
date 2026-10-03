import Chapter9AdaptedTimeIntegral

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- From conditional generator increments to the martingale identity for
 the full compensated process. All past integrals are proved measurable. -/
theorem compensated_process_martingale {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ r,F r≤m)
    (U a : ℝ → Ω → ℝ) (b : ℝ) (hb : 0≤b)
    (hU : ∀ r∈Icc 0 b,Measurable[F r] (U r))
    (hUi : ∀ r∈Icc 0 b,Integrable (U r) P)
    (ha : ∀ r∈Icc 0 b,Measurable[F r] (a r))
    (hac : ∀ w,ContinuousOn (fun r => a r w) (Icc 0 b))
    (ham : Measurable (fun z : ℝ × Ω => a z.1 z.2))
    (C : ℝ) (hbound : ∀ r∈Icc 0 b,∀ w,‖a r w‖≤C)
    (hinc : ∀ s t,0≤s → s<t → t≤b →
      P[(fun w => U t w-∫ h,a (s+h) w ∂volume.restrict (Ioc 0 (t-s)))|F s]=ᵐ[P] U s)
    (s t : ℝ) (hs : 0≤s) (hst : s≤t) (htb : t≤b) :
    P[(fun w => U t w-U 0 w-∫ r in 0..t,a r w)|F s]=ᵐ[P]
      (fun w => U s w-U 0 w-∫ r in 0..s,a r w) := by
  letI : MeasurableSpace Ω := m
  have hsb : s≤b := hst.trans htb
  have ht : 0≤t := hs.trans hst
  have hIm r (hr : r∈Icc 0 b) : Measurable[F r] (fun w => ∫ u in 0..r,a u w) :=
    measurable_past_integral (m := F r) a r hr.1
      (fun u hu => (ha u ⟨hu.1,hu.2.trans hr.2⟩).mono (hF hu.2) le_rfl)
      (fun w => (hac w).mono (Icc_subset_Icc le_rfl hr.2))
  have hIi r (hr : r∈Icc 0 b) : Integrable (fun w => ∫ u in 0..r,a u w) P :=
    integrable_bounded_time_integral P a ham r hr.1 C
      (fun u hu => hbound u ⟨hu.1.le,hu.2.trans hr.2⟩)
  have hM r (hr : r∈Icc 0 b) : Measurable[F r] (fun w => U r w-U 0 w-∫ u in 0..r,a u w) :=
    ((hU r hr).sub ((hU 0 ⟨le_rfl,hb⟩).mono (hF hr.1) le_rfl)).sub (hIm r hr)
  have hMi r (hr : r∈Icc 0 b) : Integrable (fun w => U r w-U 0 w-∫ u in 0..r,a u w) P :=
    ((hUi r hr).sub (hUi 0 ⟨le_rfl,hb⟩)).sub (hIi r hr)
  rcases hst.eq_or_lt with heq | hst
  · subst t
    exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (hle s)
      (hM s ⟨hs,hsb⟩).stronglyMeasurable (hMi s ⟨hs,hsb⟩))
  have hshift w : (∫ h,a (s+h) w ∂volume.restrict (Ioc 0 (t-s)))=
      (∫ r in 0..t,a r w)-(∫ r in 0..s,a r w) := by
    rw [← intervalIntegral.integral_of_le (sub_nonneg.mpr hst.le),
      intervalIntegral.integral_comp_add_left (fun r => a r w) s,add_zero,add_sub_cancel]
    have hit : IntervalIntegrable (fun r => a r w) volume 0 t :=
      ((hac w).mono (Icc_subset_Icc le_rfl htb)).intervalIntegrable_of_Icc ht
    have his : IntervalIntegrable (fun r => a r w) volume 0 s :=
      ((hac w).mono (Icc_subset_Icc le_rfl hsb)).intervalIntegrable_of_Icc hs
    have hist : IntervalIntegrable (fun r => a r w) volume s t :=
      ((hac w).mono (Icc_subset_Icc hs htb)).intervalIntegrable_of_Icc hst.le
    linarith [intervalIntegral.integral_add_adjacent_intervals his hist]
  let V := fun w => U t w-((∫ r in 0..t,a r w)-(∫ r in 0..s,a r w))
  let Q := fun w => U 0 w+(∫ r in 0..s,a r w)
  have hV : Integrable V P := (hUi t ⟨ht,htb⟩).sub ((hIi t ⟨ht,htb⟩).sub (hIi s ⟨hs,hsb⟩))
  have hQ : Integrable Q P := (hUi 0 ⟨le_rfl,hb⟩).add (hIi s ⟨hs,hsb⟩)
  have hmQ : Measurable[F s] Q :=
    ((hU 0 ⟨le_rfl,hb⟩).mono (hF hs) le_rfl).add (hIm s ⟨hs,hsb⟩)
  have hv : P[V|F s]=ᵐ[P] U s := by
    simpa only [hshift,V] using hinc s t hs hst htb
  have he := condExp_sub hV hQ (F s)
  have hq := condExp_of_stronglyMeasurable (hle s) hmQ.stronglyMeasurable hQ
  have hfun : (fun w => U t w-U 0 w-∫ r in 0..t,a r w)=(fun w => V w-Q w) := by
    funext w
    dsimp [V,Q]
    ring
  rw [hfun]
  filter_upwards [he,hv] with w hw hvw
  change P[V-Q|F s] w = _
  rw [hw]
  change P[V|F s] w-P[Q|F s] w = _
  rw [hq,hvw]
  dsimp [Q]
  ring
end Asakura.Chapter9
