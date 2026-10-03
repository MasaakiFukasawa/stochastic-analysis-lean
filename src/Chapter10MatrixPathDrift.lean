import Chapter10MatrixDriftCorrection
import Chapter10MatrixIntegralPath

open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Drift subtraction for actual finite matrix-integral paths. The drift
may be stopped at the endpoint: only local integrability is required. -/
theorem matrix_path_drift_correction {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcm : Monotone c) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (T : ℝ) (hT : 0≤T) (X Y : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (U Z : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (H : Fin d → Fin r → HalfClosedTime → ℝ)
    (hH : ∀ i j t,t<⊤ → ContinuousAt (H i j) t)
    (hU : MatrixIntegralPathWitness P F c hc T hT X H U)
    (hZ : MatrixIntegralPathWitness P F c hc T hT Y H Z)
    (BV : Fin r → HalfClosedTime → Ω → ℝ)
    (hB : ∀ k,SemimartingaleDecomposition P F (BV k) (BV k) (fun _ _ => 0))
    (hYX : ∀ w k t,t<⊤ → Y w (finitePrefixTime T hT t) k=
      X w (finitePrefixTime T hT t) k+BV k t w)
    (b : Fin r → ℝ → Ω → ℝ) (hbm : ∀ k w,Measurable (fun t => b k t w))
    (hbi : ∀ k w a d,IntervalIntegrable (fun t => b k t w) volume a d)
    (hBint : ∀ k w t,0≤t → BV k (realTimeClamp t) w=∫ s in 0..t,b k s w) :
    ∀ᵐ w ∂P,∀ t : Icc (0:ℝ) T,∀ i,U w t i=Z w t i-
      ∫ s in 0..t.val,∑ k,H i k (realTimeClamp s)*b k s w := by
  obtain ⟨A,M,N,hX,hN,hUsum⟩ := hU.representation
  obtain ⟨D,Q,L,hY,hL,hZsum⟩ := hZ.representation
  have he i := matrix_drift_correction P F hF hle hnull
    (fun k t w => X w (finitePrefixTime T hT t) k)
    (fun k t w => Y w (finitePrefixTime T hT t) k) BV A D M Q (N i) (L i)
    hX hY hB hYX b hbm hbi hBint (H i) (hH i) c hc hcm hcT hcc (hN i) (hL i)
  filter_upwards [ae_all_iff.mpr he] with w hw
  intro t i
  rw [hUsum,hZsum]
  exact hw i t.val t.property.1

end Asakura.Chapter10
