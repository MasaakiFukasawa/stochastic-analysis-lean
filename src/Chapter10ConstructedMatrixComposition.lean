import Chapter10MatrixIntegralComposition
import Chapter10ConstructedMatrixInverse
import Chapter3ContinuousIntegralConstruction

open MeasureTheory Set Filter Matrix
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Construct both sides of actual matrix integral associativity. Auxiliary nested integrals are constructed, rather than assumed. -/
theorem constructed_matrix_integral_composition {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r : ℕ} (i : Fin d)
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (Y A M : Fin r → HalfClosedTime → Ω → ℝ)
    (I A1 M1 : Fin r → Fin r → HalfClosedTime → Ω → ℝ)
    (hY : ∀ k,SemimartingaleDecomposition P F (Y k) (A k) (M k))
    (hI : ∀ j k,SemimartingaleDecomposition P F (I j k) (A1 j k) (M1 j k))
    (D : HalfClosedTime → Matrix (Fin d) (Fin r) ℝ)
    (J : HalfClosedTime → Matrix (Fin r) (Fin r) ℝ)
    (hD : ∀ j t,t<⊤ → ContinuousAt (fun s => D s i j) t)
    (hJ : ∀ j k t,t<⊤ → ContinuousAt (fun s => J s j k) t)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcm : Monotone c) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hA1 : ∀ j k,VariationIntegralFormula P c hc (A k) (fun z => J (realTimeClamp z.2) j k) (A1 j k))
    (hM1 : ∀ j k,ItoCovarianceFormula P F (M k) (fun z => J (realTimeClamp z.2) j k) (M1 j k)) :
    ∃ Z V : Fin r → HalfClosedTime → Ω → ℝ,
      (∀ j,SemimartingaleIntegralFormula P F c hc (fun t w => ∑ k,A1 j k t w)
        (fun t w => ∑ k,M1 j k t w) (fun z => D (realTimeClamp z.2) i j) (Z j)) ∧
      (∀ k,SemimartingaleIntegralFormula P F c hc (A k) (M k)
        (fun z => (D (realTimeClamp z.2)*J (realTimeClamp z.2)) i k) (V k)) ∧
      ∀ᵐ w ∂P,∀ t,t<⊤ → (∑ j,Z j t w)=∑ k,V k t w := by
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
  have hv k := deterministic_integral_exists P F hF hle hnull _ _ _ (hY k)
    (fun s => (D s*J s) i k) (fun t ht => by
      change ContinuousAt (fun s => ∑ j,D s i j*J s j k) t
      exact tendsto_finset_sum _ (fun j _ => (hD j t ht).mul (hJ j k t ht))) c hc hcm hcT hcc
  choose V hV using hv
  exact ⟨Z,V,hZ,hV,matrix_integral_composition P i F hF hle hnull Y A M I A1 M1 L U Z V
    hY hI D J hD hJ c hc hcT hcc hA1 hM1 hZ hL hU hV⟩

end Asakura.Chapter10
