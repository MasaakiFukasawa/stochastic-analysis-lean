import Chapter10ObservationDriftIntegral
import Mathlib.Data.Matrix.Mul

open MeasureTheory Set Filter Matrix
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Entrywise actual stochastic integrals against the predicted observation
drift combine into the ordinary integral of the matrix product H C m. -/
theorem matrix_observation_drift_integral {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r q : ℕ} (i : Fin q)
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤mΩ)
    (hnull : ∀ t E,MeasurableSet[mΩ] E → P E=0 → MeasurableSet[F t] E)
    (B Z : Fin r → HalfClosedTime → Ω → ℝ)
    (H : ℝ → Matrix (Fin q) (Fin r) ℝ) (C : ℝ → Matrix (Fin r) (Fin d) ℝ)
    (m : ℝ → Ω → Fin d → ℝ) (hH : Continuous H) (hC : Continuous C)
    (hm : ∀ w,Continuous (fun t => m t w))
    (hB : ∀ j w t,0≤t → B j (realTimeClamp t) w=∫ s in 0..t,(C s*ᵥm s w) j)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hZ : ∀ j,SemimartingaleIntegralFormula P F c hc (B j) (fun _ _ => 0)
      (fun z => H z.2 i j) (Z j)) :
    ∀ᵐ w ∂P,∀ t,0≤t → (∑ j,Z j (realTimeClamp t) w)=
      ∫ s in 0..t,((H s*C s)*ᵥm s w) i := by
  have hHc j : Continuous (fun t => H t i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hH)
  have hbc j w : Continuous (fun t => (C t*ᵥm t w) j) := by
    simp only [Matrix.mulVec,dotProduct]
    apply continuous_finset_sum
    intro k _
    exact ((continuous_apply k).comp ((continuous_apply j).comp hC)).mul
      ((continuous_apply k).comp (hm w))
  have hz j := observation_drift_integral P F hF hle hnull (B j) (Z j)
    (fun t w => (C t*ᵥm t w) j) (fun t => H t i j) (hbc j) (hHc j) (hB j)
    c hc hcT hcc (hZ j)
  filter_upwards [ae_all_iff.mpr hz] with w hw
  intro t ht
  simp_rw [hw _ t ht]
  have hi j : IntervalIntegrable (fun s => H s i j*(C s*ᵥm s w) j) volume 0 t :=
    ((hHc j).mul (hbc j w)).intervalIntegrable 0 t
  have hsum := intervalIntegral.integral_finsetSum (s := Finset.univ) (fun j _ => hi j)
  rw [←hsum]
  apply intervalIntegral.integral_congr
  intro s _
  change (H s*ᵥ(C s*ᵥm s w)) i=((H s*C s)*ᵥm s w) i
  rw [Matrix.mulVec_mulVec]

end Asakura.Chapter10
