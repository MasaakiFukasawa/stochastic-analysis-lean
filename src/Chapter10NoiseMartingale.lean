import Chapter10L2DominatedLocalMartingale
import Chapter10DeterministicNoisePath

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A deterministic Brownian integral, stopped at a finite deterministic time,
is a true square-integrable martingale. -/
theorem deterministic_noise_martingale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (B : BrownianSystem P n)
    (j : Fin n) (g : ℝ → ℝ) (hg : Continuous g)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W j) (fun z => g z.2) N)
    (T : ℝ) (hT : 0≤T) :
    ContinuousMpWitness P B.F 2 (fun t w => N (min (realTimeClamp T) t) w) := by
  obtain ⟨Z,_,hZ,he,_⟩ := deterministic_noise_path P B j g hg N hN hNI T hT
  apply finite_l2_dominated_local_martingale P B.F B.mono B.le N hN T hT
    (fun w => ‖Z w‖) hZ.norm
  apply ae_of_all
  intro w t
  have hh := he w (finitePrefixTime T hT t)
  rw [finite_prefix_time_clamp T hT le_top] at hh
  rw [← hh]
  exact (Z w).norm_coe_le_norm _

end Asakura.Chapter10
