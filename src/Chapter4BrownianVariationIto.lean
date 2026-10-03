import Chapter5ZeroIto
import Chapter4FiniteCovarianceSum
import Chapter3VariationIntegratorCongruence

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- C2 Ito for a local martingale and an adapted continuous variation path,
with all integrals constructed and all zero covariance terms removed. -/
theorem martingale_variation_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (W Y A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hY : AdaptedLocalVariationWitness F Y)
    (hYc : ∀ w t,t<⊤ → ContinuousAt (fun s => Y s w) t)
    (hA : LocalCovarianceWitness P F W W A)
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n)) :
    let V := fun t w => ![W t w,Y t w]
    ∃ N D J : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W
        (fun z => fderiv ℝ φ (V (realTimeClamp z.2) z.1) (Pi.single 0 1)) N ∧
      VariationIntegralFormula P c hc Y
        (fun z => fderiv ℝ φ (V (realTimeClamp z.2) z.1) (Pi.single 1 1)) D ∧
      VariationIntegralFormula P c hc A
        (fun z => fderiv ℝ (fderiv ℝ φ) (V (realTimeClamp z.2) z.1)
          (Pi.single 0 1) (Pi.single 0 1)) J ∧
      ∀ᵐ w ∂P,∀ t,t<⊤ → φ (V t w)=φ (V ⊥ w)+N t w+D t w+J t w/2 := by
  classical
  dsimp only
  let XX : Fin 2 → ClosedTime T → Ω → ℝ := ![W,Y]
  let AA : Fin 2 → ClosedTime T → Ω → ℝ := ![(fun _ _ => 0),Y]
  let MM : Fin 2 → ClosedTime T → Ω → ℝ := ![W,(fun _ _ => 0)]
  let CC := fun (i j : Fin 2) => if i=0 ∧ j=0 then A else (fun _ _ => 0)
  have hx i : SemimartingaleDecomposition P F (XX i) (AA i) (MM i) := by
    fin_cases i
    · exact ⟨(by change AdaptedLocalVariationWitness F (fun _ _ => 0); simpa only [zero_mul] using hY.smul 0),hW,hW.path P F,fun _ _ _ => by simp [XX,AA,MM]⟩
    · exact ⟨hY,zero_local_process P hT F,hYc,fun _ _ _ => by simp [XX,AA,MM]⟩
  have hcv i j : LocalCovarianceWitness P F (MM i) (MM j) (CC i j) := by
    fin_cases i <;> fin_cases j
    · exact hA
    · exact (zero_covariance_left P hT F hF hle W).symm P F
    · exact zero_covariance_left P hT F hF hle W
    · exact zero_covariance_left P hT F hF hle _
  obtain ⟨Z,J,hZ,hJ,he⟩ := constructed_multivariate_ito P hT F hF hle hnull
    XX AA MM CC hx hcv φ hφ c hc hcm hcT hcc
  have hjz i j (hij : ¬(i=0 ∧ j=0)) : ∀ᵐ w ∂P,∀ t,t<⊤ → J i j t w=0 := by
    have hj := hJ i j
    simp only [CC,if_neg hij] at hj
    exact hj.unique P c hc hcc _ _ (fun _ _ => 0) _ (zero_variation_integral P c hc _)
  obtain ⟨D0,N,h0,hD0,hN⟩ := hZ 0
  have hd0 := hD0.unique P c hc hcc _ _ (fun _ _ => 0) _ (zero_variation_integral P c hc _)
  obtain ⟨D,N1,h1,hD,hN1⟩ := hZ 1
  have hn1 := integral_against_zero_martingale P hT F hF hle hnull N1 _ h1.martingale hN1
  have hvec t w : (fun i => XX i t w)=![W t w,Y t w] := by ext i; fin_cases i <;> rfl
  refine ⟨N,D,J 0 0,h0.martingale,?_,?_,?_,?_⟩
  · simpa only [hvec,MM,Matrix.cons_val_zero] using hN
  · simpa only [hvec,AA,Matrix.cons_val_one,Matrix.cons_val_zero] using hD
  · simpa only [hvec,CC,ite_true,and_self] using hJ 0 0
  filter_upwards [he,hd0,hn1,hjz 0 1 (by decide),hjz 1 0 (by decide),hjz 1 1 (by decide)]
    with w hw hdw hnw h01 h10 h11
  intro t ht
  have hh := hw t ht
  simp only [Fin.sum_univ_two] at hh
  rw [h0.decomposition t ht w,h1.decomposition t ht w,hdw t ht,hnw t ht] at hh
  simpa only [hvec,Fin.sum_univ_two,h01 _ ht,h10 _ ht,h11 _ ht,zero_add,add_zero,add_assoc] using hh

end Asakura.Chapter4
