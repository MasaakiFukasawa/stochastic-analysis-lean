import Chapter7ClockODE
import Chapter7ClockInverseStopping
import Chapter7ClockHalfTime

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000

lemma finite_clock_clamp_coordinate (t : HalfClosedTime) (ht : t < ⊤) :
    realTimeClamp (halfTimeReal t) = t := by
  obtain ⟨r,hr,_,rfl⟩ := finite_closed_time_real t ht
  rw [changed_time_real r hr]

/-- Positivity in the clock ODE supplies the strict monotonicity needed
by the stochastic time-change construction on the original time space. -/
theorem strict_clock_of_ode
    (A : HalfClosedTime → ℝ)
    (hc : ∀ t,t < ⊤ → ContinuousAt A t)
    (v : ℝ → ℝ) (hvn : ∀ s,0 < s → v s ≠ 0)
    (hd : ∀ s,0 < s → HasDerivAt (fun r => A (realTimeClamp r)) (1/(v s)^2) s) :
    StrictMonoOn A (Iio ⊤) := by
  have hreal : ContinuousOn (fun r => A (realTimeClamp r)) (Ici 0) := by
    intro r hr
    exact ((hc _ (changed_time_finite r hr)).comp real_time_clamp_continuous.continuousAt).continuousWithinAt
  have hs := ode_clock_strictMono _ v hreal hvn hd
  intro a ha b hb hab
  obtain ⟨r,hr,_,rfl⟩ := finite_closed_time_real a ha
  obtain ⟨s,ht,_,rfl⟩ := finite_closed_time_real b hb
  apply hs hr ht
  change (realTimeClamp r : EReal) < (realTimeClamp s : EReal) at hab
  rw [real_time_clamp_eq r hr le_top,real_time_clamp_eq s ht le_top,EReal.coe_lt_coe_iff] at hab
  exact hab

/-- Apply the inverse differentiation result to the actual infimum clock.
The inverse and its continuity are constructed, not extra ODE hypotheses. -/
theorem inverse_clock_ode_connection
    (A : HalfClosedTime → ℝ)
    (hm : StrictMonoOn A (Iio ⊤))
    (hc : ∀ t,t < ⊤ → ContinuousAt A t) (hz : A ⊥ = 0)
    (hu : ∀ r : ℝ,∃ t,t < ⊤ ∧ r < A t)
    (v : ℝ → ℝ) (hv : Continuous v) (hvn : ∀ s,0 < s → v s ≠ 0)
    (hd : ∀ s,0 < s → HasDerivAt (fun r => A (realTimeClamp r)) (1/(v s)^2) s) :
    let τ := fun r => (halfTimeReal (inverseRealClock A r):ℝ)
    (∀ r,0 < r → HasDerivAt τ ((v (τ r))^2) r) ∧
    (∀ r,0 ≤ r → τ r = ∫ u in 0..r,(v (τ u))^2) := by
  let τ := fun r => (halfTimeReal (inverseRealClock A r):ℝ)
  have hT : (0:EReal) < ⊤ := by simp
  have hp := real_clock_inverse_properties hT A hm.monotoneOn hc hz hu
  have hτc : Continuous τ := real_clock_changed_path_continuous hT A hm.monotoneOn hc hz hu
    (fun t => (halfTimeReal t:ℝ)) changed_time_coordinate_continuousAt
    (fun a b ha hb he => by rw [hm.injOn ha hb he])
  have hτ0 : τ 0 = 0 := by simp only [τ,hp.2.1]; rfl
  have hinv r (hr : 0 ≤ r) : A (realTimeClamp (τ r)) = r := by
    rw [finite_clock_clamp_coordinate _ (hp.2.2.1 r),hp.2.2.2.1,max_eq_right hr]
  have hτp r (hr : 0 < r) : 0 < τ r := by
    have hn : 0 ≤ τ r := (halfTimeReal _).property
    by_contra h
    have he : τ r = 0 := le_antisymm (le_of_not_gt h) hn
    have hi := hinv r hr.le
    rw [he] at hi
    have hzero : realTimeClamp (T := (⊤:EReal)) 0 = ⊥ := by
      apply Subtype.ext
      exact real_time_clamp_eq 0 le_rfl le_top
    rw [hzero,hz] at hi
    exact (ne_of_gt hr) hi.symm
  apply inverse_clock_ode_integral (fun r => A (realTimeClamp r)) τ v hτc.continuousOn hτ0
    hτp hinv hvn hd
  intro r hr
  exact ((hv.comp hτc).pow 2).intervalIntegrable 0 r

end Asakura.Chapter7
