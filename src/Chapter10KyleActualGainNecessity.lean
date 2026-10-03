import Chapter4FiniteItoSum

import Chapter4BrownianSystem
import Chapter10KyleGainNecessity
import Chapter4DeterministicItoEnergy
import Chapter10SemimartingaleAlgebra

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- If the rational price has both the candidate-price and filter
semimartingale equations, uniqueness of their martingale parts and the actual
Ito energy identity force the continuous filter gain to equal Kyle's lambda. -/
theorem kyle_actual_gain_necessity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (W C X A D N : HalfClosedTime → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w r,0≤r → C (realTimeClamp r) w=r)
    (k : ℝ → ℝ) (hk : Continuous k) (l σ T : ℝ) (hσ : σ≠0) (hT : 0<T)
    (hX : SemimartingaleDecomposition P F X A (fun t w => (l*σ)*W t w))
    (hR : SemimartingaleDecomposition P F X D N)
    (hNI : ItoCovarianceFormula P F W (fun z => k z.2*σ) N) :
    ∀ t∈Icc 0 T,k t=l := by
  have he := hX.unique P F hF hle hR
  have hi := deterministic_brownian_integral_difference_energy P (by simp : (0:EReal)<⊤)
    F hF hle hnull W C N (fun t w => (l*σ)*W t w) hW hC hR.martingale hX.martingale
    (fun w r hr _ => hclock w r hr) (fun s => k s*σ) (fun _ => l*σ)
    (hk.mul_const σ) continuous_const hNI
    (constant_ito_integral P (by simp : (0:EReal)<⊤) F hF hle hnull W hW (l*σ))
    T hT.le (EReal.coe_lt_top T)
  have hz : (∫ w,(N (realTimeClamp T) w-(l*σ)*W (realTimeClamp T) w)^2 ∂P)=0 := by
    trans ∫ _ : Ω,(0:ℝ) ∂P
    · apply integral_congr_ae
      filter_upwards [he] with w hw
      rw [←(hw _ (real_time_below T hT.le (EReal.coe_lt_top T))).2]
      simp
    · simp
  have henergy : (∫ s in 0..T,(k s-l)^2*σ^2)=0 := by
    rw [hz] at hi
    calc
      _ = ∫ s in 0..T,(k s*σ-l*σ)^2 := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only
        ring
      _ = 0 := hi.symm
  exact continuous_gain_of_zero_energy k T l σ hT hσ hk.continuousOn henergy

end Asakura.Chapter10
