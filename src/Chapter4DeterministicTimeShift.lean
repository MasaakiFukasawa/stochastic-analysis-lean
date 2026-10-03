import Chapter4LocalTimeChange
import Chapter2HalfLineLocalization

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable def deterministicTimeShift (s : ℝ) (hs : 0≤s) (t : HalfClosedTime) : HalfClosedTime :=
  ⟨(s:EReal)+t.val,add_nonneg (EReal.coe_le_coe hs) t.property.1,le_top⟩
noncomputable def deterministicTimeUnshift (s : ℝ) (t : HalfClosedTime) : HalfClosedTime :=
  ⟨max 0 (t.val-(s:EReal)),le_max_left _ _,le_top⟩

lemma deterministic_shift_mono (s : ℝ) (hs : 0≤s) : Monotone (deterministicTimeShift s hs) := by
  intro a b hab
  change (s:EReal)+a.val≤(s:EReal)+b.val
  exact add_le_add le_rfl hab
lemma deterministic_unshift_mono (s : ℝ) : Monotone (deterministicTimeUnshift s) :=
  fun _ _ h => max_le_max le_rfl (EReal.sub_le_sub h le_rfl)

lemma deterministic_shift_continuous (s : ℝ) (hs : 0≤s) : Continuous (deterministicTimeShift s hs) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top s)) (Or.inl (EReal.coe_ne_bot s))).comp
    (continuous_const.prodMk continuous_subtype_val).continuousAt

lemma deterministic_unshift_continuous (s : ℝ) : Continuous (deterministicTimeUnshift s) := by
  apply Continuous.subtype_mk
  apply continuous_const.max
  apply continuous_iff_continuousAt.mpr
  intro t
  change ContinuousAt (fun t : HalfClosedTime => t.val+(-(s:EReal))) t
  exact (EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))).comp
    (continuous_subtype_val.prodMk continuous_const).continuousAt

lemma deterministic_shift_adjunction (s : ℝ) (hs : 0≤s) (a t : HalfClosedTime) :
    deterministicTimeUnshift s a≤t ↔ a≤deterministicTimeShift s hs t := by
  change max 0 (a.val-(s:EReal))≤t.val ↔ a.val≤(s:EReal)+t.val
  rw [max_le_iff,and_iff_right t.property.1]
  simpa only [add_comm] using EReal.sub_le_iff_le_add (a:=a.val) (b:=(s:EReal)) (c:=t.val)
    (Or.inl (EReal.coe_ne_bot s)) (Or.inl (EReal.coe_ne_top s))

lemma deterministic_shift_section (s : ℝ) (hs : 0≤s) (a : HalfClosedTime) :
    deterministicTimeShift s hs (deterministicTimeUnshift s a)=max (deterministicTimeShift s hs ⊥) a := by
  apply Subtype.ext
  change (s:EReal)+max 0 (a.val-(s:EReal))=max ((s:EReal)+0) a.val
  have hm : Monotone (fun x : EReal => (s:EReal)+x) := fun _ _ h => add_le_add le_rfl h
  rw [hm.map_max]
  congr 1
  rw [add_comm,EReal.sub_add_cancel]

lemma deterministic_shift_below_top (s : ℝ) (hs : 0≤s) (t : HalfClosedTime) (ht : t<⊤) :
    deterministicTimeShift s hs t<⊤ := EReal.add_lt_top (EReal.coe_ne_top s) (ne_of_lt ht)
lemma deterministic_unshift_below_top (s : ℝ) (t : HalfClosedTime) (ht : t<⊤) :
    deterministicTimeUnshift s t<⊤ := by
  change max 0 (t.val-(s:EReal))<⊤
  apply max_lt (EReal.coe_lt_top 0)
  exact EReal.add_lt_top (ne_of_lt ht) (by simp)

lemma deterministic_shift_real (s : ℝ) (hs : 0≤s) (r : ℝ) (hr : 0≤r) :
    deterministicTimeShift s hs (realTimeClamp (T:=⊤) r)=realTimeClamp (T:=⊤) (s+r) := by
  apply Subtype.ext
  change (s:EReal)+(realTimeClamp (T:=⊤) r).val=(realTimeClamp (T:=⊤) (s+r)).val
  rw [real_time_clamp_eq r hr le_top,real_time_clamp_eq (s+r) (add_nonneg hs hr) le_top,EReal.coe_add]

/-- The future increment process is an actual local martingale in the
shifted filtration. This is the stochastic part of restarting an SDE. -/
theorem local_martingale_shifted_future
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X : HalfClosedTime → Ω → ℝ) (hX : LocalMProcessWitness P F X) (s : ℝ) (hs : 0≤s) :
    LocalMProcessWitness P (fun t => F (deterministicTimeShift s hs t))
      (fun t w => X (deterministicTimeShift s hs t) w-X (deterministicTimeShift s hs ⊥) w) :=
  local_martingale_time_change_increment P F hF hle (deterministicTimeShift s hs) (deterministicTimeUnshift s)
    (deterministic_shift_mono s hs) (deterministic_shift_continuous s hs) (deterministic_unshift_mono s)
    (deterministic_shift_adjunction s hs) (deterministic_shift_section s hs)
    (deterministic_shift_below_top s hs) (deterministic_unshift_below_top s) X hX

end Asakura.Chapter4
