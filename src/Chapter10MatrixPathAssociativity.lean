import Chapter10MatrixIntegralPathLift
import Chapter10ActualMatrixComposition

open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Associativity for the actual finite continuous matrix-integral paths,
including different chosen decompositions and null-set identifications. -/
theorem matrix_path_integral_associativity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcm : Monotone c) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (T : ℝ) (hT : 0≤T)
    (Y Z : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (U V : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (H : Fin r → Fin r → HalfClosedTime → ℝ)
    (K : Fin d → Fin r → HalfClosedTime → ℝ)
    (hH : ∀ i j t,t<⊤ → ContinuousAt (H i j) t)
    (hK : ∀ i j t,t<⊤ → ContinuousAt (K i j) t)
    (hZ : MatrixIntegralPathWitness P F c hc T hT Y H Z)
    (hU : MatrixIntegralPathWitness P F c hc T hT Z K U)
    (hV : MatrixIntegralPathWitness P F c hc T hT Y (fun i k s => ∑ j,K i j s*H j k s) V) :
    U=ᵐ[P] V := by
  obtain ⟨A,M,N,hY,hN,hZsum⟩ := hZ.representation
  obtain ⟨DA,DM,O,hQ,hO,hUsum⟩ := hU.representation
  obtain ⟨VA,VM,W,hY',hW,hVsum⟩ := hV.representation
  have hex : ∀ j k,∃ A1 M1,SemimartingaleDecomposition P F (N j k) A1 M1 ∧
      VariationIntegralFormula P c hc (A k) (fun z => H j k (realTimeClamp z.2)) A1 ∧
      ItoCovarianceFormula P F (M k) (fun z => H j k (realTimeClamp z.2)) M1 := hN
  choose A1 M1 hI hA1 hM1 using hex
  have hQeq := matrix_integral_path_lift P F hF hle hnull T hT Y A M hY H hH
    c hc hcT hcc N hN Z hZsum
  let Y' := fun k (t : HalfClosedTime) w => Y w (finitePrefixTime T hT t) k
  let Z' := fun k (t : HalfClosedTime) w => Z w (finitePrefixTime T hT t) k
  let D : HalfClosedTime → Matrix (Fin d) (Fin r) ℝ := fun s i j => K i j s
  let J : HalfClosedTime → Matrix (Fin r) (Fin r) ℝ := fun s i j => H i j s
  have hprod i k t (ht : t<⊤) : ContinuousAt (fun s => (D s*J s) i k) t := by
    change ContinuousAt (fun s => ∑ j,K i j s*H j k s) t
    exact tendsto_finset_sum _ (fun j _ => (hK i j t ht).mul (hH j k t ht))
  have hve i k := deterministic_integral_exists P F hF hle hnull _ _ _ (hY k)
    (fun s => (D s*J s) i k) (hprod i k) c hc hcm hcT hcc
  choose V' hV' using hve
  have hcomp i := actual_matrix_integral_composition P i F hF hle hnull Y' A M N A1 M1
    hY hI Z' DA DM (O i) hQ hQeq D J (hK i) hH c hc hcm hcT hcc hA1 hM1
    (hO i) (V' i) (hV' i)
  have he i k := deterministic_integral_unique P F hF hle hnull (Y' k) (A k) (M k)
    (VA k) (VM k) (V' i k) (W i k) (hY k) (hY' k)
    (fun s => (D s*J s) i k) (hprod i k) c hc hcT hcc (hV' i k) (hW i k)
  filter_upwards [ae_all_iff.mpr hcomp,ae_all_iff.mpr (fun i => ae_all_iff.mpr (he i))]
    with w hw hew
  apply ContinuousMap.ext
  intro t
  funext i
  rw [hUsum,hVsum,hw i _ (half_real_time_finite t.val)]
  simp_rw [hew i _ _ (half_real_time_finite t.val)]

end Asakura.Chapter10
