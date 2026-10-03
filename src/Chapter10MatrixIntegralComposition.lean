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

/-- Matrix associativity for the actual component stochastic integrals.
This supplies the K D part of the innovation reconstruction as well as D. -/
theorem matrix_integral_composition {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r : ℕ} (i : Fin d)
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (Y A M : Fin r → HalfClosedTime → Ω → ℝ)
    (I A1 M1 L U : Fin r → Fin r → HalfClosedTime → Ω → ℝ)
    (Z : Fin r → HalfClosedTime → Ω → ℝ) (V : Fin r → HalfClosedTime → Ω → ℝ)
    (hY : ∀ k,SemimartingaleDecomposition P F (Y k) (A k) (M k))
    (hI : ∀ j k,SemimartingaleDecomposition P F (I j k) (A1 j k) (M1 j k))
    (D : HalfClosedTime → Matrix (Fin d) (Fin r) ℝ)
    (J : HalfClosedTime → Matrix (Fin r) (Fin r) ℝ)
    (hD : ∀ j t,t<⊤ → ContinuousAt (fun s => D s i j) t)
    (hJ : ∀ j k t,t<⊤ → ContinuousAt (fun s => J s j k) t)
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
    (hV : ∀ k,SemimartingaleIntegralFormula P F c hc (A k) (M k)
      (fun z => (D (realTimeClamp z.2)*J (realTimeClamp z.2)) i k) (V k)) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → (∑ j,Z j t w)=∑ k,V k t w := by
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
  have hflat k : ∀ᵐ w ∂P,∀ t,t<⊤ → V k t w=∑ j,U j k t w := by
    apply finite_deterministic_integral_linearity P F hF hle hnull
      (fun _ : Fin r => Y k) (fun _ => A k) (fun _ => M k) (fun j => U j k)
      (Y k) (A k) (M k) (V k) (fun _ => hY k) (hY k)
      (fun j s => D s i j*J s j k) (fun s => (D s*J s) i k)
      (fun j s hs => (hD j s hs).mul (hJ j k s hs))
      (fun s hs => by
        change ContinuousAt (fun s => ∑ j,D s i j*J s j k) s
        exact tendsto_finset_sum _ (fun j _ => (hD j s hs).mul (hJ j k s hs)))
      c hc hcT hcc (fun j => hU j k) (hV k)
    intro w s t _ _
    change (∑ j,D s i j*J s j k)*(Y k t w-Y k s w)=_
    rw [Finset.sum_mul]
  filter_upwards [ae_all_iff.mpr hz,ae_all_iff.mpr (fun j => ae_all_iff.mpr (ha j)),
    ae_all_iff.mpr hflat] with w hz ha hf
  intro t ht
  calc
    _ = ∑ j,∑ k,U j k t w := by simp_rw [hz _ t ht,ha _ _ t ht]
    _ = ∑ k,∑ j,U j k t w := Finset.sum_comm
    _ = ∑ k,V k t w := by simp_rw [←hf _ t ht]

end Asakura.Chapter10
