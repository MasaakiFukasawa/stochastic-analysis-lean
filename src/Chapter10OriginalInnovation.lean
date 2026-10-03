import Chapter10MatrixPathInverse
import Chapter10MatrixPathDrift

open MeasureTheory Set Filter Matrix
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Starting with residual observation R = integral b + D dot W, the
innovation defined as J dot R really equals integral J b + W. The noise
cancellation uses actual matrix integrals and J D = 1. -/
theorem original_innovation_identity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {r : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcm : Monotone c) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (T : ℝ) (hT : 0≤T) (W Z R U I : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (D J : Fin r → Fin r → HalfClosedTime → ℝ)
    (hD : ∀ i j t,t<⊤ → ContinuousAt (D i j) t)
    (hJ : ∀ i j t,t<⊤ → ContinuousAt (J i j) t)
    (hZ : MatrixIntegralPathWitness P F c hc T hT W D Z)
    (hU : MatrixIntegralPathWitness P F c hc T hT Z J U)
    (hI : MatrixIntegralPathWitness P F c hc T hT R J I)
    (hinv : ∀ s : HalfClosedTime,s<⊤ →
      (show Matrix (Fin r) (Fin r) ℝ from fun i j => J i j s)*
        (show Matrix (Fin r) (Fin r) ℝ from fun i j => D i j s)=1)
    (hzero : ∀ w,W w ⟨0,le_rfl,hT⟩=0)
    (BV : Fin r → HalfClosedTime → Ω → ℝ)
    (hB : ∀ k,SemimartingaleDecomposition P F (BV k) (BV k) (fun _ _ => 0))
    (hR : ∀ w k t,t<⊤ → R w (finitePrefixTime T hT t) k=
      Z w (finitePrefixTime T hT t) k+BV k t w)
    (b : Fin r → ℝ → Ω → ℝ) (hbm : ∀ k w,Measurable (fun t => b k t w))
    (hbi : ∀ k w a d,IntervalIntegrable (fun t => b k t w) volume a d)
    (hBint : ∀ k w t,0≤t → BV k (realTimeClamp t) w=∫ s in 0..t,b k s w) :
    ∀ᵐ w ∂P,∀ t : Icc (0:ℝ) T,∀ i,
      I w t i=(∫ s in 0..t.val,∑ k,J i k (realTimeClamp s)*b k s w)+W w t i := by
  have hnoise := matrix_path_integral_inverse P F hF hle hnull c hc hcm hcT hcc T hT
    W Z U D J hD hJ hZ hU hinv hzero
  have hdrift := matrix_path_drift_correction P F hF hle hnull c hc hcm hcT hcc T hT
    Z R U I J hJ hU hI BV hB hR b hbm hbi hBint
  filter_upwards [hnoise,hdrift] with w hw hd
  intro t i
  have hh := hd t i
  rw [hw] at hh
  linarith

end Asakura.Chapter10
