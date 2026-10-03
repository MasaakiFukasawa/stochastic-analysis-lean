import Chapter2ContinuousVariationAssociativity
import Chapter2ItoAssociativityConstruction
import Chapter2SemimartingaleIntegralConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def SemimartingaleIntegralFormula
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (A M : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ) (Y : ClosedTime T → Ω → ℝ) : Prop :=
  ∃ I J, SemimartingaleDecomposition P F Y I J ∧
    VariationIntegralFormula P c hc A H I ∧ ItoCovarianceFormula P F M H J

theorem SemimartingaleIntegralFormula.unique
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (A M Y Z : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hM : LocalMProcessWitness P F M)
    (hY : SemimartingaleIntegralFormula P F c hc A M H Y)
    (hZ : SemimartingaleIntegralFormula P F c hc A M H Z) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → Y t ω = Z t ω := by
  obtain ⟨I,J,hYD,hI,hJ⟩ := hY
  obtain ⟨K,L,hZD,hK,hL⟩ := hZ
  have heA := hI.unique P c hc hcc A I K H hK
  have heM := hJ.unique P hT F hF hle hnull M J L H hM hYD.martingale hZD.martingale hL
  filter_upwards [heA,heM] with ω hAω hMω
  intro t ht
  rw [hYD.decomposition t ht ω,hZD.decomposition t ht ω,hAω t ht,hMω t ht]

/-- The entire associativity exercise for continuous semimartingales:
all three integrals are constructed, their original A_loc/M_loc
memberships are proved, and the two component identities are combined. -/
theorem semimartingale_associativity_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (H G : Ω × ℝ → ℝ)
    (hHa : ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun ω => H (ω,r)))
    (hGa : ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun ω => G (ω,r)))
    (hHc : ∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ ω, ContinuousOn (fun r => H (ω,r)) (Icc 0 b))
    (hGc : ∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ ω, ContinuousOn (fun r => G (ω,r)) (Icc 0 b)) :
    ∃ (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n),
      (∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n)) ∧
      ∃ A1 M1 Y2 Y3 : ClosedTime T → Ω → ℝ,
        SemimartingaleDecomposition P F (fun t ω => A1 t ω+M1 t ω) A1 M1 ∧
        VariationIntegralFormula P c hc A G A1 ∧ ItoCovarianceFormula P F M G M1 ∧
        SemimartingaleIntegralFormula P F c hc A1 M1 H Y2 ∧
        SemimartingaleIntegralFormula P F c hc A M (fun z => H z*G z) Y3 ∧
        (∀ᵐ ω ∂P, ∀ t, t < ⊤ → Y2 t ω = Y3 t ω) := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨A1,A2,A3,hA1,hA2,hA3,hA1c,hA2c,hA3c,hAG,hAH,hAHG,heA⟩ :=
    continuous_variation_associativity_constructed P F hF hnull c (fun n => (hc n).le)
      hcm.monotone hcT hcc A hX.variation (hX.variation_continuous P F) H G hHa hGa hHc hGc
  obtain ⟨M1,M2,M3,hM1,hM2,hM3,hMG,hMH,hMHG,heM⟩ :=
    continuous_adapted_ito_associativity_constructed P hT F hF hle hnull M hX.martingale
      G H hGa hHa hGc hHc
  have hD1 : SemimartingaleDecomposition P F (fun t ω => A1 t ω+M1 t ω) A1 M1 :=
    ⟨hA1,hM1,fun ω t ht => (hA1c ω t ht).add (hM1.path P F ω t ht),fun _ _ _ => rfl⟩
  have hD2 : SemimartingaleDecomposition P F (fun t ω => A2 t ω+M2 t ω) A2 M2 :=
    ⟨hA2,hM2,fun ω t ht => (hA2c ω t ht).add (hM2.path P F ω t ht),fun _ _ _ => rfl⟩
  have hD3 : SemimartingaleDecomposition P F (fun t ω => A3 t ω+M3 t ω) A3 M3 :=
    ⟨hA3,hM3,fun ω t ht => (hA3c ω t ht).add (hM3.path P F ω t ht),fun _ _ _ => rfl⟩
  refine ⟨c,fun n => (hc n).le,hcc,A1,M1,_,_,hD1,hAG,hMG,
    ⟨A2,M2,hD2,hAH,hMH⟩,⟨A3,M3,hD3,hAHG,hMHG⟩,?_⟩
  filter_upwards [heA,heM] with ω hAω hMω
  intro t ht
  change A2 t ω+M2 t ω = A3 t ω+M3 t ω
  rw [hAω t ht,hMω t ht]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.semimartingale_associativity_constructed
