import Chapter10MatrixPathAssociativity
import Chapter10MatrixPathInverse
import Chapter10MatrixPathDrift
import Chapter10MatrixPathCoefficient

open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- All three stochastic-integral reconstruction identities follow from the
actual definitions: I=J dot(Y-B), (KD) dot I=K dot Y-K dot B,
and D dot I=Y-B. The residual R=Y-B is retained as an actual process. -/
theorem kalman_integral_reconstruction {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcm : Monotone c) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (T : ℝ) (hT : 0≤T) (Y R I ZJY ZDI : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (ZKY ZKR ZKDI : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (D J : HalfClosedTime → Matrix (Fin r) (Fin r) ℝ)
    (K : HalfClosedTime → Matrix (Fin d) (Fin r) ℝ)
    (hD : ∀ i j t,t<⊤ → ContinuousAt (fun s => D s i j) t)
    (hJ : ∀ i j t,t<⊤ → ContinuousAt (fun s => J s i j) t)
    (hK : ∀ i j t,t<⊤ → ContinuousAt (fun s => K s i j) t)
    (hinv : ∀ t,t<⊤ → D t*J t=1)
    (hI : MatrixIntegralPathWitness P F c hc T hT R (fun i j s => J s i j) I)
    (hDI : MatrixIntegralPathWitness P F c hc T hT I (fun i j s => D s i j) ZDI)
    (hKDI : MatrixIntegralPathWitness P F c hc T hT I (fun i j s => (K s*D s) i j) ZKDI)
    (hKR : MatrixIntegralPathWitness P F c hc T hT R (fun i j s => K s i j) ZKR)
    (hKY : MatrixIntegralPathWitness P F c hc T hT Y (fun i j s => K s i j) ZKY)
    (hJY : MatrixIntegralPathWitness P F c hc T hT Y (fun i j s => J s i j) ZJY)
    (hR0 : ∀ w,R w ⟨0,le_rfl,hT⟩=0)
    (BV : Fin r → HalfClosedTime → Ω → ℝ)
    (hB : ∀ k,SemimartingaleDecomposition P F (BV k) (BV k) (fun _ _ => 0))
    (hYR : ∀ w k t,t<⊤ → Y w (finitePrefixTime T hT t) k=
      R w (finitePrefixTime T hT t) k+BV k t w)
    (b : Fin r → ℝ → Ω → ℝ) (hbm : ∀ k w,Measurable (fun t => b k t w))
    (hbi : ∀ k w a d,IntervalIntegrable (fun t => b k t w) volume a d)
    (hBint : ∀ k w t,0≤t → BV k (realTimeClamp t) w=∫ s in 0..t,b k s w) :
    ∀ᵐ w ∂P,∀ t : Icc (0:ℝ) T,
      (∀ i,I w t i=ZJY w t i-∫ s in 0..t.val,∑ k,J (realTimeClamp s) i k*b k s w) ∧
      (∀ i,ZKDI w t i=ZKY w t i-∫ s in 0..t.val,∑ k,K (realTimeClamp s) i k*b k s w) ∧
      ZDI w t=R w t := by
  have hji := matrix_path_drift_correction P F hF hle hnull c hc hcm hcT hcc T hT R Y I ZJY
    (fun i j s => J s i j) hJ hI hJY BV hB hYR b hbm hbi hBint
  have hki := matrix_path_drift_correction P F hF hle hnull c hc hcm hcT hcc T hT R Y ZKR ZKY
    (fun i j s => K s i j) hK hKR hKY BV hB hYR b hbm hbi hBint
  have hprod : MatrixIntegralPathWitness P F c hc T hT R
      (fun i k s => ∑ j,(K s*D s) i j*J s j k) ZKR :=
    hKR.congr_coefficient P F c hc hcT T hT R _ _ ZKR (by
      intro i k s hs
      change K s i k=((K s*D s)*J s) i k
      rw [Matrix.mul_assoc,hinv s hs,Matrix.mul_one])
  have hKD i j t (ht : t<⊤) : ContinuousAt (fun s => (K s*D s) i j) t := by
    change ContinuousAt (fun s => ∑ k,K s i k*D s k j) t
    exact tendsto_finset_sum _ (fun k _ => (hK i k t ht).mul (hD k j t ht))
  have hassoc := matrix_path_integral_associativity P F hF hle hnull c hc hcm hcT hcc T hT
    R I ZKDI ZKR (fun i j s => J s i j) (fun i j s => (K s*D s) i j) hJ hKD hI hKDI hprod
  have hinverse := matrix_path_integral_inverse P F hF hle hnull c hc hcm hcT hcc T hT R I ZDI
    (fun i j s => J s i j) (fun i j s => D s i j) hJ hD hI hDI hinv hR0
  filter_upwards [hji,hki,hassoc,hinverse] with w hj hk ha hd
  intro t
  refine ⟨hj t,?_,?_⟩
  · rw [ha]
    exact hk t
  · rw [hd]

end Asakura.Chapter10
