import Chapter10ConstructedMatrixInverse
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
theorem actual_matrix_observation_inverse {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {r : ℕ} (i : Fin r)
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (Y A M : Fin r → HalfClosedTime → Ω → ℝ)
    (I A1 M1 : Fin r → Fin r → HalfClosedTime → Ω → ℝ)
    (hY : ∀ k,SemimartingaleDecomposition P F (Y k) (A k) (M k))
    (hI : ∀ j k,SemimartingaleDecomposition P F (I j k) (A1 j k) (M1 j k))
    (Q DA DM Z : Fin r → HalfClosedTime → Ω → ℝ)
    (hQ : ∀ j,SemimartingaleDecomposition P F (Q j) (DA j) (DM j))
    (hQeq : ∀ᵐ w ∂P,∀ t,t<⊤ → ∀ j,Q j t w=∑ k,I j k t w)
    (D J : HalfClosedTime → Matrix (Fin r) (Fin r) ℝ)
    (hD : ∀ j t,t<⊤ → ContinuousAt (fun s => D s i j) t)
    (hJ : ∀ j k t,t<⊤ → ContinuousAt (fun s => J s j k) t)
    (hinv : ∀ t,t<⊤ → D t*J t=1)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcm : Monotone c) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hA1 : ∀ j k,VariationIntegralFormula P c hc (A k) (fun z => J (realTimeClamp z.2) j k) (A1 j k))
    (hM1 : ∀ j k,ItoCovarianceFormula P F (M k) (fun z => J (realTimeClamp z.2) j k) (M1 j k))
    (hZ : ∀ j,SemimartingaleIntegralFormula P F c hc (DA j) (DM j)
      (fun z => D (realTimeClamp z.2) i j) (Z j)) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → (∑ j,Z j t w)=Y i t w-Y i ⊥ w := by
  obtain ⟨V,hV,hrecover⟩ := constructed_matrix_observation_inverse P i F hF hle hnull
    Y A M I A1 M1 hY hI D J hD hJ hinv c hc hcm hcT hcc hA1 hM1
  have hsum j : SemimartingaleDecomposition P F (fun t w => ∑ k,I j k t w)
      (fun t w => ∑ k,A1 j k t w) (fun t w => ∑ k,M1 j k t w) := by
    simpa only [one_mul] using semimartingale_weighted_sum P (by simp : (0:EReal)<⊤)
      F hF hle (I j) (A1 j) (M1 j) (fun _ => 1) (hI j)
  have he j := deterministic_integral_congr_ae P F hF hle hnull _ (Q j) _ _ (DA j) (DM j)
    (V j) (Z j) (hsum j) (hQ j) (hQeq.mono (fun w hw t ht => hw t ht j))
    (fun s => D s i j) (hD j) c hc hcT hcc (hV j) (hZ j)
  filter_upwards [ae_all_iff.mpr he,hrecover] with w hw hr
  intro t ht
  simp_rw [hw _ t ht]
  exact hr t ht

end Asakura.Chapter10
