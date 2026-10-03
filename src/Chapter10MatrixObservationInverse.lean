import Chapter10ActualIntegralAssociativity
import Chapter10FiniteIntegralLinearity
import Chapter10SemimartingaleFiniteMap
import Chapter8BrownianForcingPath

open MeasureTheory Set Filter Matrix
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Undo an invertible deterministic observation matrix using the actual
component stochastic integrals. Linearity, associativity and the unit
integral identity are proved separately from the original integral definition. -/
theorem matrix_observation_inverse {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {r : ℕ} (i : Fin r)
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (Y A M : Fin r → HalfClosedTime → Ω → ℝ)
    (I A1 M1 L U : Fin r → Fin r → HalfClosedTime → Ω → ℝ)
    (Z : Fin r → HalfClosedTime → Ω → ℝ) (V : HalfClosedTime → Ω → ℝ)
    (hY : ∀ k,SemimartingaleDecomposition P F (Y k) (A k) (M k))
    (hI : ∀ j k,SemimartingaleDecomposition P F (I j k) (A1 j k) (M1 j k))
    (D J : HalfClosedTime → Matrix (Fin r) (Fin r) ℝ)
    (hD : ∀ j t,t<⊤ → ContinuousAt (fun s => D s i j) t)
    (hJ : ∀ j k t,t<⊤ → ContinuousAt (fun s => J s j k) t)
    (hinv : ∀ t,t<⊤ → D t*J t=1)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hA1 : ∀ j k,VariationIntegralFormula P c hc (A k) (fun z => J (realTimeClamp z.2) j k) (A1 j k))
    (hM1 : ∀ j k,ItoCovarianceFormula P F (M k) (fun z => J (realTimeClamp z.2) j k) (M1 j k))
    (hZ : ∀ j,SemimartingaleIntegralFormula P F c hc (fun t w => ∑ k,A1 j k t w)
      (fun t w => ∑ k,M1 j k t w) (fun z => D (realTimeClamp z.2) i j) (Z j))
    (hL : ∀ j k,SemimartingaleIntegralFormula P F c hc (A1 j k) (M1 j k)
      (fun z => D (realTimeClamp z.2) i j) (L j k))
    (hU : ∀ j k,SemimartingaleIntegralFormula P F c hc (A k) (M k)
      (fun z => D (realTimeClamp z.2) i j*J (realTimeClamp z.2) j k) (U j k))
    (hV : SemimartingaleIntegralFormula P F c hc (A i) (M i) (fun _ => 1) V) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → (∑ j,Z j t w)=Y i t w-Y i ⊥ w := by
  have hsum j : SemimartingaleDecomposition P F (fun t w => ∑ k,I j k t w)
      (fun t w => ∑ k,A1 j k t w) (fun t w => ∑ k,M1 j k t w) := by
    simpa only [one_mul] using semimartingale_weighted_sum P (by simp : (0:EReal)<⊤)
      F hF hle (I j) (A1 j) (M1 j) (fun _ => 1) (hI j)
  have hz j : ∀ᵐ w ∂P,∀ t,t<⊤ → Z j t w=∑ k,L j k t w := by
    apply finite_deterministic_integral_linearity P F hF hle hnull
      (I j) (A1 j) (M1 j) (L j) _ _ _ (Z j) (hI j) (hsum j)
      (fun _ s => D s i j) (fun s => D s i j) (fun _ => hD j) (hD j)
      c hc hcT hcc (hL j) (hZ j)
    intro w s t _ _
    rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  have hDm j : Measurable (fun s : ℝ => D (realTimeClamp s) i j) := by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (hD j _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  have hJm j k : Measurable (fun s : ℝ => J (realTimeClamp s) j k) := by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (hJ j k _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  have ha j k : ∀ᵐ w ∂P,∀ t,t<⊤ → L j k t w=U j k t w :=
    actual_semimartingale_integral_associativity P F hF hle hnull (Y k) (A k) (M k)
      (I j k) (A1 j k) (M1 j k) (L j k) (U j k) (hY k) (hI j k)
      _ _ (hDm j) (hJm j k) c hc hcT hcc (hA1 j k) (hM1 j k) (hL j k) (hU j k)
  have hflat : ∀ᵐ w ∂P,∀ t,t<⊤ → V t w=∑ z : Fin r × Fin r,U z.1 z.2 t w := by
    apply finite_deterministic_integral_linearity P F hF hle hnull
      (fun z : Fin r × Fin r => Y z.2) (fun z => A z.2) (fun z => M z.2) (fun z => U z.1 z.2)
      (Y i) (A i) (M i) V (fun z => hY z.2) (hY i)
      (fun z s => D s i z.1*J s z.1 z.2) (fun _ => 1)
      (fun z s hs => (hD z.1 s hs).mul (hJ z.1 z.2 s hs)) (fun _ _ => continuousAt_const)
      c hc hcT hcc (fun z => hU z.1 z.2) hV
    intro w s t hs _
    rw [one_mul,Fintype.sum_prod_type,Finset.sum_comm]
    simp only [←Finset.sum_mul]
    have he k : (∑ j,D s i j*J s j k)=(1 : Matrix (Fin r) (Fin r) ℝ) i k :=
      congrArg (fun Q : Matrix (Fin r) (Fin r) ℝ => Q i k) (hinv s hs)
    simp_rw [he]
    change Y i t w-Y i s w=∑ k,(if i=k then (1:ℝ) else 0)*(Y k t w-Y k s w)
    simp
  have hid := deterministic_integral_identity P F hF hle hnull (Y i) (A i) (M i) V (hY i)
    c hc hcT hcc hV
  filter_upwards [ae_all_iff.mpr hz,ae_all_iff.mpr (fun j => ae_all_iff.mpr (ha j)),hflat,hid]
    with w hz ha hf hi
  intro t ht
  calc
    _ = ∑ j,∑ k,U j k t w := by simp_rw [hz _ t ht,ha _ _ t ht]
    _ = V t w := by simpa only [Fintype.sum_prod_type] using (hf t ht).symm
    _ = _ := hi t ht

end Asakura.Chapter10
