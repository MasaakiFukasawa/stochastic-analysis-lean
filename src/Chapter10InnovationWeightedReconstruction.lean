import Chapter10ActualMatrixComposition
import Chapter10LocallyIntegrableDriftCorrection
import Chapter10DeterministicIntegralUniqueness
import Chapter10ConstructedMatrixComposition
import Chapter10DeterministicIntegralCongruence
import Chapter3ContinuousIntegralConstruction

open MeasureTheory Set Filter Matrix
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Given the actual entry integrals J dot Y, construct the inverse integral
D dot (J dot Y) and prove it recovers Y-Y0. Auxiliary nested integrals are
constructed here, not assumed as additional input. -/
theorem innovation_weighted_reconstruction {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r : ℕ} (i : Fin d)
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (Y A M : Fin r → HalfClosedTime → Ω → ℝ)
    (I A1 M1 : Fin r → Fin r → HalfClosedTime → Ω → ℝ)
    (hY : ∀ k,SemimartingaleDecomposition P F (Y k) (A k) (M k))
    (hI : ∀ j k,SemimartingaleDecomposition P F (I j k) (A1 j k) (M1 j k))
    (Q DA DM Z : Fin r → HalfClosedTime → Ω → ℝ)
    (hQ : ∀ j,SemimartingaleDecomposition P F (Q j) (DA j) (DM j))
    (hQeq : ∀ᵐ w ∂P,∀ t,t<⊤ → ∀ j,Q j t w=∑ k,I j k t w)
    (D : HalfClosedTime → Matrix (Fin d) (Fin r) ℝ)
    (J : HalfClosedTime → Matrix (Fin r) (Fin r) ℝ)
    (hD : ∀ j t,t<⊤ → ContinuousAt (fun s => D s i j) t)
    (hJ : ∀ j k t,t<⊤ → ContinuousAt (fun s => J s j k) t)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcm : Monotone c) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hA1 : ∀ j k,VariationIntegralFormula P c hc (A k) (fun z => J (realTimeClamp z.2) j k) (A1 j k))
    (hM1 : ∀ j k,ItoCovarianceFormula P F (M k) (fun z => J (realTimeClamp z.2) j k) (M1 j k))
    (hZ : ∀ j,SemimartingaleIntegralFormula P F c hc (DA j) (DM j)
      (fun z => D (realTimeClamp z.2) i j) (Z j))
    (V : Fin r → HalfClosedTime → Ω → ℝ)
    (hV : ∀ k,SemimartingaleIntegralFormula P F c hc (A k) (M k)
      (fun z => (D (realTimeClamp z.2)*J (realTimeClamp z.2)) i k) (V k))
    (O OA OM BV ZO : Fin r → HalfClosedTime → Ω → ℝ)
    (hO : ∀ k,SemimartingaleDecomposition P F (O k) (OA k) (OM k))
    (hBV : ∀ k,SemimartingaleDecomposition P F (BV k) (BV k) (fun _ _ => 0))
    (hOY : ∀ w k t,t<⊤ → O k t w=Y k t w+BV k t w)
    (b : Fin r → ℝ → Ω → ℝ)
    (hbm : ∀ k w,Measurable (fun t => b k t w))
    (hbi : ∀ k w a d,IntervalIntegrable (fun t => b k t w) volume a d)
    (hBint : ∀ k w t,0≤t → BV k (realTimeClamp t) w=∫ s in 0..t,b k s w)
    (hZO : ∀ k,SemimartingaleIntegralFormula P F c hc (OA k) (OM k)
      (fun z => (D (realTimeClamp z.2)*J (realTimeClamp z.2)) i k) (ZO k)) :
    ∀ᵐ w ∂P,∀ t,0≤t → (∑ j,Z j (realTimeClamp t) w)=
      (∑ k,ZO k (realTimeClamp t) w)-
        ∫ s in 0..t,∑ k,(D (realTimeClamp s)*J (realTimeClamp s)) i k*b k s w := by
  have hcomp := actual_matrix_integral_composition P i F hF hle hnull Y A M I A1 M1
    hY hI Q DA DM Z hQ hQeq D J hD hJ c hc hcm hcT hcc hA1 hM1 hZ V hV
  let H := fun k s => (D s*J s) i k
  have hH k t (ht : t<⊤) : ContinuousAt (H k) t := by
    change ContinuousAt (fun s => ∑ j,D s i j*J s j k) t
    exact tendsto_finset_sum _ (fun j _ => (hD j t ht).mul (hJ j k t ht))
  have hHr k : Continuous (fun s : ℝ => H k (realTimeClamp s)) :=
    continuous_iff_continuousAt.mpr fun s =>
      (hH k _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  have hcorr k : ∀ᵐ w ∂P,∀ t,0≤t → V k (realTimeClamp t) w=
      ZO k (realTimeClamp t) w-∫ s in 0..t,H k (realTimeClamp s)*b k s w := by
    obtain ⟨ZB,hZB⟩ := deterministic_integral_exists P F hF hle hnull _ _ _ (hBV k)
      (H k) (hH k) c hc hcm hcT hcc
    exact observation_locally_integrable_drift_correction P F hF hle hnull
      (Y k) (O k) (BV k) (A k) (OA k) (M k) (OM k) (V k) ZB (ZO k)
      (hY k) (hO k) (hBV k) (fun w t ht => hOY w k t ht)
      (b k) (hbm k) (hbi k) (hBint k) (H k) (hH k) c hc hcT hcc (hV k) hZB (hZO k)
  filter_upwards [hcomp,ae_all_iff.mpr hcorr] with w hw hc'
  intro t ht
  rw [hw _ (half_real_time_finite t)]
  simp_rw [hc' _ t ht]
  rw [Finset.sum_sub_distrib]
  congr 1
  symm
  exact intervalIntegral.integral_finsetSum (fun k _ =>
    (hbi k w 0 t).continuousOn_mul (hHr k).continuousOn)

end Asakura.Chapter10
