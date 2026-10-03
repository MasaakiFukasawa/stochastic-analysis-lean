import Chapter2LevelLocalization
import Chapter7ClockHalfTime
import Chapter13FubiniEnergy

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000

/-- First crossings of the accumulated finite energy give stopping times,
no overshoot, and an exhausting localization. -/
theorem bounded_energy_localizers {Ω:Type*}
    (F:ClosedTime (⊤:EReal) → MeasurableSpace Ω) (hF:Monotone F)
    (C:ClosedTime (⊤:EReal) → Ω → ℝ)
    (hCm:∀t,Measurable[F t] (C t)) (hCc:∀w,Continuous (fun t => C t w))
    (hC0:∀w,C ⊥ w=0) (K:Ω → ℝ) (hK:∀t w,C t w≤K w) :
    let τ:=fun (n:ℕ) w => sInf {t | (n:ℝ)+1≤C t w}
    (∀n t,MeasurableSet[F t] {w | τ n w≤t}) ∧
    (∀w,Monotone (fun n:ℕ => τ n w)) ∧
    (∀n w t,C (min (τ n w) t) w≤(n:ℝ)+1) ∧
    (∀w,∃N:ℕ,∀n,N≤n → τ n w=⊤) := by
  intro τ
  refine ⟨?_,?_,?_,?_⟩
  · intro n
    exact continuous_hitting_stopping_written F hF C hCm hCc (Ici ((n:ℝ)+1)) isClosed_Ici
  · intro w i j hij
    apply sInf_le_sInf
    intro t ht
    have hij':(i:ℝ)≤j := by exact_mod_cast hij
    change (i:ℝ)+1≤C t w
    change (j:ℝ)+1≤C t w at ht
    linarith
  · intro n w t
    exact continuous_level_stop_bound (fun t => C t w) (hCc w) ((n:ℝ)+1)
      (by rw [hC0];positivity) _ (min_le_left _ _)
  · intro w
    obtain ⟨N,hN⟩:=exists_nat_gt (K w)
    refine ⟨N,fun n hn => ?_⟩
    have hn':(N:ℝ)≤n := by exact_mod_cast hn
    have he:{t | (n:ℝ)+1≤C t w}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hh:=hK t w
      change (n:ℝ)+1≤C t w at ht
      linarith
    change sInf {t | (n:ℝ)+1≤C t w}=⊤
    rw [he,sInf_empty]
end Asakura.Chapter13
#print axioms Asakura.Chapter13.bounded_energy_localizers
