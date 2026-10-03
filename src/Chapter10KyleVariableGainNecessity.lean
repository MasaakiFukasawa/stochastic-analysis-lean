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
theorem kyle_variable_gain_necessity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (W C X A D N M : HalfClosedTime → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w r,0≤r → C (realTimeClamp r) w=r)
    (k l : ℝ → ℝ) (hk : Continuous k) (hl : Continuous l) (σ T : ℝ) (hσ : σ≠0) (hT : 0<T)
    (hX : SemimartingaleDecomposition P F X A M)
    (hMI : ItoCovarianceFormula P F W (fun z => l z.2*σ) M)
    (hR : SemimartingaleDecomposition P F X D N)
    (hNI : ItoCovarianceFormula P F W (fun z => k z.2*σ) N) :
    ∀ t∈Icc 0 T,k t=l t := by
  have he := hX.unique P F hF hle hR
  have hi := deterministic_brownian_integral_difference_energy P (by simp : (0:EReal)<⊤)
    F hF hle hnull W C N M hW hC hR.martingale hX.martingale
    (fun w r hr _ => hclock w r hr) (fun s => k s*σ) (fun s => l s*σ)
    (hk.mul_const σ) (hl.mul_const σ) hNI hMI
    T hT.le (EReal.coe_lt_top T)
  have hz : (∫ w,(N (realTimeClamp T) w-M (realTimeClamp T) w)^2 ∂P)=0 := by
    trans ∫ _ : Ω,(0:ℝ) ∂P
    · apply integral_congr_ae
      filter_upwards [he] with w hw
      rw [←(hw _ (real_time_below T hT.le (EReal.coe_lt_top T))).2]
      simp
    · simp
  have henergy : (∫ s in 0..T,(k s-l s)^2*σ^2)=0 := by
    rw [hz] at hi
    calc
      _ = ∫ s in 0..T,(k s*σ-l s*σ)^2 := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only
        ring
      _ = 0 := hi.symm
  have hz := continuous_gain_of_zero_energy (fun s => k s-l s) T 0 σ hT hσ
    (hk.sub hl).continuousOn (by simpa only [sub_zero] using henergy)
  intro t ht
  exact sub_eq_zero.mp (hz t ht)

end Asakura.Chapter10
