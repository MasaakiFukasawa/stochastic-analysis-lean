import Chapter10MatrixIntegralPathLift
import Chapter10ActualMatrixInverse

open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Associativity for the actual finite continuous matrix-integral paths,
including different chosen decompositions and null-set identifications. -/
theorem matrix_path_integral_inverse {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {r : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcm : Monotone c) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (T : ℝ) (hT : 0≤T)
    (Y Z : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (U : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (H : Fin r → Fin r → HalfClosedTime → ℝ)
    (K : Fin r → Fin r → HalfClosedTime → ℝ)
    (hH : ∀ i j t,t<⊤ → ContinuousAt (H i j) t)
    (hK : ∀ i j t,t<⊤ → ContinuousAt (K i j) t)
    (hZ : MatrixIntegralPathWitness P F c hc T hT Y H Z)
    (hU : MatrixIntegralPathWitness P F c hc T hT Z K U)
    (hinv : ∀ s : HalfClosedTime,s<⊤ →
      (show Matrix (Fin r) (Fin r) ℝ from fun i j => K i j s)*
        (show Matrix (Fin r) (Fin r) ℝ from fun i j => H i j s)=1)
    (hzero : ∀ w,Y w ⟨0,le_rfl,hT⟩=0) :
    U=ᵐ[P] Y := by
  obtain ⟨A,M,N,hY,hN,hZsum⟩ := hZ.representation
  obtain ⟨DA,DM,O,hQ,hO,hUsum⟩ := hU.representation
  have hex : ∀ j k,∃ A1 M1,SemimartingaleDecomposition P F (N j k) A1 M1 ∧
      VariationIntegralFormula P c hc (A k) (fun z => H j k (realTimeClamp z.2)) A1 ∧
      ItoCovarianceFormula P F (M k) (fun z => H j k (realTimeClamp z.2)) M1 := hN
  choose A1 M1 hI hA1 hM1 using hex
  have hQeq := matrix_integral_path_lift P F hF hle hnull T hT Y A M hY H hH
    c hc hcT hcc N hN Z hZsum
  let Y' := fun k (t : HalfClosedTime) w => Y w (finitePrefixTime T hT t) k
  let Z' := fun k (t : HalfClosedTime) w => Z w (finitePrefixTime T hT t) k
  let D := fun s i j => K i j s
  let J := fun s i j => H i j s
  have hcomp i := actual_matrix_observation_inverse P i F hF hle hnull Y' A M N A1 M1
    hY hI Z' DA DM (O i) hQ hQeq D J (hK i) hH hinv c hc hcm hcT hcc hA1 hM1 (hO i)
  have hbot : finitePrefixTime (T := (⊤:EReal)) T hT ⊥=⟨0,le_rfl,hT⟩ := by
    apply Subtype.ext
    change (min (0:EReal) (T:EReal)).toReal=0
    rw [min_eq_left (by exact_mod_cast hT)]
    rfl
  filter_upwards [ae_all_iff.mpr hcomp] with w hw
  apply ContinuousMap.ext
  intro t
  funext i
  rw [hUsum,hw i _ (half_real_time_finite t.val)]
  dsimp only [Y']
  rw [hbot,hzero,Pi.zero_apply,sub_zero]
  have ht : finitePrefixTime T hT (realTimeClamp t.val)=t :=
    Subtype.ext (finite_prefix_time_of_real T t.val hT t.property le_top)
  rw [ht]

end Asakura.Chapter10
