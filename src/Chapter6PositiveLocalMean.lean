import Chapter6ExponentialClosed

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- A positive shifted local martingale has mean at most its initial value
at every stopping time strictly below the terminal time. -/
theorem positive_shifted_local_mean_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (L : ClosedTime T → Ω → ℝ) (hL : LocalMProcessWitness P F L)
    (hb : ∀ᵐ w ∂P,∀ t,t < ⊤ → -(1:ℝ) ≤ L t w)
    (τ : Ω → ClosedTime T) (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t})
    (hτt : ∀ w,τ w < ⊤) :
    Integrable (fun w => L (τ w) w+1) P ∧
      (∫⁻ w,ENNReal.ofReal (L (τ w) w+1) ∂P) ≤ 1 := by
  obtain ⟨_,hi,_,hz,hineq⟩ := lower_bounded_local_stopped_supermartingale P F hF hle L hL τ hτ hτt 1 hb
  have hi' : Integrable (fun w => L (τ w) w) P := by simpa only [min_top_right] using hi ⊤
  have hzero : (∫ w,L ⊥ w ∂P) = 0 := by
    simpa only [min_bot_right,Pi.zero_apply,integral_zero] using integral_congr_ae hz
  have hle' : (∫ w,L (τ w) w ∂P) ≤ 0 := by
    have hh := hineq ⊥ ⊤ bot_le univ MeasurableSet.univ
    simpa only [setIntegral_univ,min_top_right,min_bot_right,hzero] using hh
  have hsum : Integrable (fun w => L (τ w) w+1) P := hi'.add (integrable_const (1:ℝ))
  refine ⟨hsum,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hsum
    (hb.mono fun w hw => by change 0 ≤ L (τ w) w+1; linarith [hw (τ w) (hτt w)]),
    integral_add hi' (integrable_const (1:ℝ))]
  have hh : (∫ w,L (τ w) w ∂P)+(∫ _w, (1:ℝ) ∂P) ≤ 1 := by simpa using hle'
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq (by simp)

end Asakura.Chapter6
