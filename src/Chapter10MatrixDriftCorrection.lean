import Chapter10LocallyIntegrableDriftCorrection
import Chapter10ConstructedMatrixInverse

open MeasureTheory Set Filter Matrix
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Subtract the prediction drift before a matrix integral. This establishes
the first innovation reconstruction equation from its actual definition. -/
theorem matrix_drift_correction {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {r : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X Y BV A D M N U Z : Fin r → HalfClosedTime → Ω → ℝ)
    (hX : ∀ k,SemimartingaleDecomposition P F (X k) (A k) (M k))
    (hY : ∀ k,SemimartingaleDecomposition P F (Y k) (D k) (N k))
    (hB : ∀ k,SemimartingaleDecomposition P F (BV k) (BV k) (fun _ _ => 0))
    (hYX : ∀ w k t,t<⊤ → Y k t w=X k t w+BV k t w)
    (b : Fin r → ℝ → Ω → ℝ) (hbm : ∀ k w,Measurable (fun t => b k t w))
    (hbi : ∀ k w a d,IntervalIntegrable (fun t => b k t w) volume a d)
    (hBint : ∀ k w t,0≤t → BV k (realTimeClamp t) w=∫ s in 0..t,b k s w)
    (H : Fin r → HalfClosedTime → ℝ) (hH : ∀ k t,t<⊤ → ContinuousAt (H k) t)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcm : Monotone c) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hU : ∀ k,SemimartingaleIntegralFormula P F c hc (A k) (M k) (fun z => H k (realTimeClamp z.2)) (U k))
    (hZ : ∀ k,SemimartingaleIntegralFormula P F c hc (D k) (N k) (fun z => H k (realTimeClamp z.2)) (Z k)) :
    ∀ᵐ w ∂P,∀ t,0≤t → (∑ k,U k (realTimeClamp t) w)=
      (∑ k,Z k (realTimeClamp t) w)-∫ s in 0..t,∑ k,H k (realTimeClamp s)*b k s w := by
  have he k : ∀ᵐ w ∂P,∀ t,0≤t → U k (realTimeClamp t) w=
      Z k (realTimeClamp t) w-∫ s in 0..t,H k (realTimeClamp s)*b k s w := by
    obtain ⟨V,hV⟩ := deterministic_integral_exists P F hF hle hnull _ _ _ (hB k)
      (H k) (hH k) c hc hcm hcT hcc
    exact observation_locally_integrable_drift_correction P F hF hle hnull
      (X k) (Y k) (BV k) (A k) (D k) (M k) (N k) (U k) V (Z k)
      (hX k) (hY k) (hB k) (fun w t ht => hYX w k t ht)
      (b k) (hbm k) (hbi k) (hBint k) (H k) (hH k) c hc hcT hcc (hU k) hV (hZ k)
  have hHr k : Continuous (fun s : ℝ => H k (realTimeClamp s)) :=
    continuous_iff_continuousAt.mpr fun s =>
      (hH k _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  filter_upwards [ae_all_iff.mpr he] with w hw
  intro t ht
  simp_rw [hw _ t ht]
  rw [Finset.sum_sub_distrib]
  congr 1
  symm
  exact intervalIntegral.integral_finsetSum (fun k _ =>
    (hbi k w 0 t).continuousOn_mul (hHr k).continuousOn)

end Asakura.Chapter10
