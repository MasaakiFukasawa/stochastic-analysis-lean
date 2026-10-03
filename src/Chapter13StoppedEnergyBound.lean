import Chapter13AccumulatedEnergy
import Chapter13StoppedEnergyExpectation

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000

/-- The stopped time-energy integral is precisely the primitive evaluated
at the stop; domination of the volatility energy by the total energy is
preserved. Applied with the first-crossing no-overshoot bound, this gives n. -/
theorem stopped_energy_bound (e g:ℝ → ℝ) (R τ K:ℝ) (hτ:τ∈Icc 0 R)
    (he:IntervalIntegrable e volume 0 R) (hg:IntervalIntegrable g volume 0 R)
    (hdom:∀r∈Icc 0 R,e r≤g r) (hb:(∫r in 0..τ,g r)≤K) :
    (∫r in 0..R,if r≤τ then e r else 0)≤K := by
  have hh:(∫r in 0..R,if r≤τ then e r else 0)=∫r in 0..τ,e r := by
    exact intervalIntegral.integral_indicator (f:=e) hτ
  rw [hh]
  have hsub:uIcc 0 τ⊆uIcc 0 R := by
    rw [uIcc_of_le hτ.1,uIcc_of_le (hτ.1.trans hτ.2)]
    exact Icc_subset_Icc_right hτ.2
  exact (intervalIntegral.integral_mono_on hτ.1 (he.mono_set hsub) (hg.mono_set hsub)
    (fun r hr => hdom r ⟨hr.1,hr.2.trans hτ.2⟩)).trans hb
end Asakura.Chapter13
#print axioms Asakura.Chapter13.stopped_energy_bound
