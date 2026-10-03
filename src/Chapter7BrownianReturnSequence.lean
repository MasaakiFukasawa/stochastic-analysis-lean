import Chapter7BrownianReturnStop

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2200000

/-- Construct all the successive delayed returns, keeping the stopping-time
property and one common full-measure event for finiteness, spacing and
vanishing of the Brownian path. -/
theorem brownian_return_sequence
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) :
    ∃ τ : ℕ → Ω → HalfClosedTime,
      (∀ n t,MeasurableSet[B.F t] {w | τ n w ≤ t}) ∧
      (∀ w,τ 0 w = ⊥) ∧
      (∀ᵐ w ∂P,∀ n,τ n w < ⊤ ∧ τ n w ≤ τ (n+1) w ∧
        (halfTimeReal (τ n w):ℝ)+1 ≤ (halfTimeReal (τ (n+1) w):ℝ) ∧
        B.W 0 (τ n w) w = 0) := by
  classical
  let S := {σ : Ω → HalfClosedTime //
    (∀ t,MeasurableSet[B.F t] {w | σ w ≤ t}) ∧ (∀ᵐ w ∂P,σ w < ⊤)}
  let init : S := ⟨fun _ => ⊥,fun t => by simp,ae_of_all _ fun _ => by
    change (0:EReal) < ⊤
    simp⟩
  have hn (s : S) := brownian_delayed_return P B s.val s.property.1 s.property.2
  let step : S → S := fun s => ⟨(hn s).choose,(hn s).choose_spec.1,
    (hn s).choose_spec.2.mono (fun _ h => h.1)⟩
  let seq : ℕ → S := fun n => (step^[n]) init
  have hs n : seq (n+1) = step (seq n) := Function.iterate_succ_apply' step n init
  let τ := fun n => (seq n).val
  have hzero : ∀ᵐ w ∂P,B.W 0 (τ 0 w) w = 0 := by
    filter_upwards [(B.martingale 0).initial P B.F] with w hw
    exact hw
  have hnext n : ∀ᵐ w ∂P,τ (n+1) w < ⊤ ∧ τ n w ≤ τ (n+1) w ∧
      (halfTimeReal (τ n w):ℝ)+1 ≤ (halfTimeReal (τ (n+1) w):ℝ) ∧
      B.W 0 (τ (n+1) w) w = 0 := by
    simpa only [τ,hs,step] using (hn (seq n)).choose_spec.2
  refine ⟨τ,fun n => (seq n).property.1,fun w => rfl,?_⟩
  filter_upwards [ae_all_iff.mpr hnext,hzero,ae_all_iff.mpr (fun n => (seq n).property.2)] with w hw hz hfin
  intro n
  refine ⟨hfin n,(hw n).2.1,(hw n).2.2.1,?_⟩
  cases n with
  | zero => exact hz
  | succ n => exact (hw n).2.2.2

end Asakura.Chapter7
