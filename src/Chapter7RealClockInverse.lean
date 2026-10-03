import Chapter7ExtendedClock

open Set Filter
open scoped Topology
namespace Asakura.Chapter7
open Asakura.Chapter2Written
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

noncomputable def inverseRealClock {T : EReal} [Fact (0 ≤ T)]
    (C : ClosedTime T → ℝ) (r : ℝ) : ClosedTime T :=
  sInf {t | ((max 0 r : ℝ) : EReal) ≤ extendedClock C t}

theorem real_clock_inverse_properties
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (C : ClosedTime T → ℝ) (hm : MonotoneOn C (Iio ⊤))
    (hc : ∀ t,t < ⊤ → ContinuousAt C t) (hz : C ⊥ = 0)
    (hu : ∀ r : ℝ,∃ t,t < ⊤ ∧ r < C t) :
    Monotone (inverseRealClock C) ∧ inverseRealClock C 0 = ⊥ ∧
    (∀ r,inverseRealClock C r < ⊤) ∧
    (∀ r,C (inverseRealClock C r) = max 0 r) ∧
    (∀ r t,t < ⊤ → (inverseRealClock C r ≤ t ↔ max 0 r ≤ C t)) := by
  have hE := extended_clock_monotone C hm
  have hEc := extended_clock_continuous C hc
  have hEr := extended_clock_right_continuous C hc
  have hEnd := extended_clock_endpoint_supremum C hu
  have hE0 : extendedClock C ⊥ = 0 := by rw [extended_clock_finite C ⊥ hT,hz]; rfl
  have hrt (r : ℝ) : ((max 0 r : ℝ) : EReal) < extendedClock C ⊤ := by
    rw [extended_clock_top]; exact EReal.coe_lt_top _
  have hfin r : inverseRealClock C r < ⊤ :=
    (generalized_inverse_before_terminal _ hEnd _ (hrt r)).1
  refine ⟨?_,?_,hfin,?_,?_⟩
  · intro r s hrs
    apply (generalized_inverse_monotone (extendedClock C)).1
    exact_mod_cast max_le_max_left 0 hrs
  · apply le_antisymm _ bot_le
    apply sInf_le
    change ((max 0 0 : ℝ) : EReal) ≤ extendedClock C ⊥
    rw [hE0]; norm_num
  · intro r
    have hlevel := (continuous_clock_inverse_levels _ hE hEc hEnd _
      (by rw [hE0]; exact_mod_cast (le_max_left 0 r)) (hrt r)).1
    change extendedClock C (inverseRealClock C r) = ((max 0 r : ℝ) : EReal) at hlevel
    rw [extended_clock_finite C _ (hfin r)] at hlevel
    exact_mod_cast hlevel
  · intro r t ht
    have he := right_continuous_inverse_event _ hE hEr ((max 0 r : ℝ) : EReal)
      ⟨⊤,(hrt r).le⟩ t
    rw [extended_clock_finite C t ht] at he
    have he' := he.not
    simpa only [not_lt,EReal.coe_le_coe_iff,inverseRealClock] using he'.symm

theorem real_clock_changed_path_continuous
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (C : ClosedTime T → ℝ) (hm : MonotoneOn C (Iio ⊤))
    (hc : ∀ t,t < ⊤ → ContinuousAt C t) (hz : C ⊥ = 0)
    (hu : ∀ r : ℝ,∃ t,t < ⊤ ∧ r < C t)
    (X : ClosedTime T → ℝ) (hX : ∀ t,t < ⊤ → ContinuousAt X t)
    (hflat : ∀ a b,a < ⊤ → b < ⊤ → C a = C b → X a = X b) :
    Continuous (fun r => X (inverseRealClock C r)) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  have hE0 : extendedClock C ⊥ = 0 := by rw [extended_clock_finite C ⊥ hT,hz]; rfl
  have hh := finite_clock_path_continuity (extendedClock C) (extended_clock_monotone C hm)
    (extended_clock_continuous C hc) (extended_clock_endpoint_supremum C hu)
    X (fun t ht => (hX t ht).continuousWithinAt)
    (fun a b ha hb he => hflat a b ha hb (by
      rw [extended_clock_finite C a ha,extended_clock_finite C b hb] at he
      exact_mod_cast he)) ((max 0 r : ℝ) : EReal)
    (by rw [hE0]; exact_mod_cast (le_max_left 0 r))
    (by rw [extended_clock_top]; exact EReal.coe_lt_top _)
  have hin : Continuous (fun u : ℝ => ((max 0 u : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (continuous_const.max continuous_id)
  exact hh.comp (f := fun u : ℝ => ((max 0 u : ℝ) : EReal)) hin.continuousAt

end Asakura.Chapter7
