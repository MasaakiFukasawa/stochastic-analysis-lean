import Chapter10ActualMatrixInverse
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
theorem innovation_observation_recovery {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {r : ℕ} (i : Fin r)
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (Y A M : Fin r → HalfClosedTime → Ω → ℝ)
    (I A1 M1 : Fin r → Fin r → HalfClosedTime → Ω → ℝ)
    (hY : ∀ k,SemimartingaleDecomposition P F (Y k) (A k) (M k))
    (hI : ∀ j k,SemimartingaleDecomposition P F (I j k) (A1 j k) (M1 j k))
    (O : Fin r → HalfClosedTime → Ω → ℝ) (b : Fin r → ℝ → Ω → ℝ)
    (hres : ∀ w k t,0≤t → Y k (realTimeClamp t) w=
      O k (realTimeClamp t) w-∫ s in 0..t,b k s w)
    (hO0 : ∀ w k,O k (realTimeClamp 0) w=0)
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
    ∀ᵐ w ∂P,∀ t,0≤t → O i (realTimeClamp t) w=
      (∫ s in 0..t,b i s w)+∑ j,Z j (realTimeClamp t) w := by
  have he := actual_matrix_observation_inverse P i F hF hle hnull Y A M I A1 M1
    hY hI Q DA DM Z hQ hQeq D J hD hJ hinv c hc hcm hcT hcc hA1 hM1 hZ
  filter_upwards [he] with w hw
  intro t ht
  have hh := hw (realTimeClamp t) (half_real_time_finite t)
  have hzero := hres w i 0 (le_refl 0)
  rw [hO0,intervalIntegral.integral_same,sub_zero] at hzero
  have hbot : realTimeClamp (T := (⊤:EReal)) 0=⊥ := Subtype.ext (real_time_clamp_eq 0 le_rfl le_top)
  rw [hres w i t ht,←hbot,hzero,sub_zero] at hh
  linarith

end Asakura.Chapter10
