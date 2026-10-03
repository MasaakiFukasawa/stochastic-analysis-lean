import Chapter10MatrixObservationInverse
import Chapter3ContinuousIntegralConstruction

open MeasureTheory Set Filter Matrix
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Construct an actual integral for any continuous deterministic coefficient
on a prescribed common time exhaustion. -/
theorem deterministic_integral_exists {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (Y A M : HalfClosedTime → Ω → ℝ) (hY : SemimartingaleDecomposition P F Y A M)
    (H : HalfClosedTime → ℝ) (hH : ∀ t,t<⊤ → ContinuousAt H t)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcm : Monotone c) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k)) :
    ∃ Z,SemimartingaleIntegralFormula P F c hc A M (fun z => H (realTimeClamp z.2)) Z := by
  obtain ⟨I,N,hZ,hI,hN⟩ := continuous_semimartingale_integral_exists P
    (by simp : (0:EReal)<⊤) F hF hle hnull Y A M (fun t _ => H t) hY
    (fun _ _ => measurable_const) (fun _ => hH) c hc hcm hcT hcc
  exact ⟨_,I,N,hZ,hI,hN⟩

/-- Given the actual entry integrals J dot Y, construct the inverse integral
D dot (J dot Y) and prove it recovers Y-Y0. Auxiliary nested integrals are
constructed here, not assumed as additional input. -/
theorem constructed_matrix_observation_inverse {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {r : ℕ} (i : Fin r)
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (Y A M : Fin r → HalfClosedTime → Ω → ℝ)
    (I A1 M1 : Fin r → Fin r → HalfClosedTime → Ω → ℝ)
    (hY : ∀ k,SemimartingaleDecomposition P F (Y k) (A k) (M k))
    (hI : ∀ j k,SemimartingaleDecomposition P F (I j k) (A1 j k) (M1 j k))
    (D J : HalfClosedTime → Matrix (Fin r) (Fin r) ℝ)
    (hD : ∀ j t,t<⊤ → ContinuousAt (fun s => D s i j) t)
    (hJ : ∀ j k t,t<⊤ → ContinuousAt (fun s => J s j k) t)
    (hinv : ∀ t,t<⊤ → D t*J t=1)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcm : Monotone c) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hA1 : ∀ j k,VariationIntegralFormula P c hc (A k) (fun z => J (realTimeClamp z.2) j k) (A1 j k))
    (hM1 : ∀ j k,ItoCovarianceFormula P F (M k) (fun z => J (realTimeClamp z.2) j k) (M1 j k)) :
    ∃ Z : Fin r → HalfClosedTime → Ω → ℝ,
      (∀ j,SemimartingaleIntegralFormula P F c hc (fun t w => ∑ k,A1 j k t w)
        (fun t w => ∑ k,M1 j k t w) (fun z => D (realTimeClamp z.2) i j) (Z j)) ∧
      ∀ᵐ w ∂P,∀ t,t<⊤ → (∑ j,Z j t w)=Y i t w-Y i ⊥ w := by
  have hsum j : SemimartingaleDecomposition P F (fun t w => ∑ k,I j k t w)
      (fun t w => ∑ k,A1 j k t w) (fun t w => ∑ k,M1 j k t w) := by
    simpa only [one_mul] using semimartingale_weighted_sum P (by simp : (0:EReal)<⊤)
      F hF hle (I j) (A1 j) (M1 j) (fun _ => 1) (hI j)
  have hz j := deterministic_integral_exists P F hF hle hnull _ _ _ (hsum j)
    (fun s => D s i j) (hD j) c hc hcm hcT hcc
  choose Z hZ using hz
  have hl j k := deterministic_integral_exists P F hF hle hnull _ _ _ (hI j k)
    (fun s => D s i j) (hD j) c hc hcm hcT hcc
  choose L hL using hl
  have hu j k := deterministic_integral_exists P F hF hle hnull _ _ _ (hY k)
    (fun s => D s i j*J s j k) (fun t ht => (hD j t ht).mul (hJ j k t ht)) c hc hcm hcT hcc
  choose U hU using hu
  obtain ⟨V,hV⟩ := deterministic_integral_exists P F hF hle hnull _ _ _ (hY i)
    (fun _ => 1) (fun _ _ => continuousAt_const) c hc hcm hcT hcc
  exact ⟨Z,hZ,matrix_observation_inverse P i F hF hle hnull Y A M I A1 M1 L U Z V
    hY hI D J hD hJ hinv c hc hcT hcc hA1 hM1 hZ hL hU hV⟩

end Asakura.Chapter10
