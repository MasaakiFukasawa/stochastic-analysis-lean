import Chapter10KalmanInnovationIdentification
import Chapter10ActualConditionalFilter
import Chapter10PathInformation
import Chapter10InnovationHistoryIdentification
import Chapter10RiccatiAlgebra

open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter9
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Substitute the manuscript's actual Kalman gain and observation inverse
into the identification of any actual error/innovation solution. -/
theorem kalman_conditional_identification {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d q r : ℕ} (B : BrownianSystem P (q+r))
    (A S : ℝ → Matrix (Fin d) (Fin d) ℝ) (G : ℝ → Matrix (Fin d) (Fin q) ℝ)
    (C : ℝ → Matrix (Fin r) (Fin d) ℝ) (D J : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (hA : Continuous A) (hS : Continuous S) (hG : Continuous G)
    (hC : Continuous C) (hD : Continuous D) (hJ : Continuous J)
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (hξ0 : ∫ w,ξ w ∂P=0) (T : ℝ) (hT : 0≤T)
    (hinit : S 0=(fun i j => ∫ w,ξ w i*ξ w j ∂P))
    (hJD : ∀ t∈Ico 0 T,J t*D t=1) (hDJ : ∀ t∈Ico 0 T,D t*J t=1)
    (hSym : ∀ t∈Ico 0 T,(S t).transpose=S t)
    (hSd : ∀ t∈Ico 0 T,HasDerivWithinAt S
      (A t*S t+S t*(A t).transpose+G t*(G t).transpose-S t*((C t).transpose*((J t).transpose*J t)*C t)*S t) (Ici t) t) :
    let K := fun t => S t*(C t).transpose*((J t).transpose*J t)
    let F := fun t => A t-K t*C t
    let U := fun t => matrixOperatorMap (finiteBlocks (F t) 0 (J t*C t) (0 : Matrix (Fin r) (Fin r) ℝ))
    let E := fun i j t => finiteBlocks (G t) (-(K t*D t)) (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ) i j
    ∀ N X,LinearStateWitness P B U E (fun w => extendZero (r := r) (ξ w)) T hT N X →
      ∀ (t : Icc (0:ℝ) T) (Y : Ω → C(Icc (0:ℝ) t.val,Fin r → ℝ)),Measurable Y →
      nullAugmentedInformation (m := m) P (MeasurableSpace.comap Y inferInstance)=
        nullAugmentedInformation (m := m) P (pathInformation T X tailIndex t) →
      ∀ a : Ω → Fin d → ℝ,
        Measurable[nullAugmentedInformation (m := m) P (MeasurableSpace.comap Y inferInstance)] a →
        (∀ i,Integrable (fun w => a w i) P) →
      (∀ i,P[(fun w => a w i+X w t (headIndex i))|
        nullAugmentedInformation (m := m) P (MeasurableSpace.comap Y inferInstance)]=ᵐ[P] fun w => a w i) ∧
      (∀ i j,P[(fun w => X w t (headIndex i)*X w t (headIndex j))|
        nullAugmentedInformation (m := m) P (MeasurableSpace.comap Y inferInstance)]=ᵐ[P] fun _ => S t.val i j) ∧
      (∀ f : (Fin d → ℝ) → ℝ,Measurable f → ∀ C : ℝ,(∀ x,‖f x‖≤C) →
        P[(fun w => f (a w+fun i => X w t (headIndex i)))|
          nullAugmentedInformation (m := m) P (MeasurableSpace.comap Y inferInstance)]=ᵐ[P]
          fun w => ∫ z,f (a w+z) ∂P.map (fun w i => X w t (headIndex i))) := by
  intro K F U E N X hX t Y hY hinfo a ha hia
  have hK : Continuous K := by dsimp [K]; fun_prop
  have hF : Continuous F := hA.sub (hK.matrix_mul hC)
  have hU : Continuous U := matrixOperatorMap.continuous.comp
    (finiteBlocks_continuous F _ (fun s => J s*C s) _ hF continuous_const
      (hJ.matrix_mul hC) continuous_const)
  have hEc : Continuous (fun s => finiteBlocks (G s) (-(K s*D s))
      (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ)) :=
    finiteBlocks_continuous G _ _ _ hG (hK.matrix_mul hD).neg continuous_const continuous_const
  have hE i j : Continuous (E i j) := (continuous_apply j).comp ((continuous_apply i).comp hEc)
  obtain ⟨_,hcov,hind⟩ := kalman_innovation_identification P B A S G C D J hA hS hG hC hD hJ
    ξ hξ hξg hξ0 T hT hinit hJD hDJ hSym hSd N X hX
  obtain ⟨hξm,hξG,hξz⟩ := augmented_initial_gaussian P (B.F ⊥) (B.le _) (r := r) ξ hξ hξg hξ0
  let I := fun w (z : {u : Icc (0:ℝ) T // u.val≤t.val} × Fin r) => X w z.1.val (tailIndex z.2)
  have hI : Measurable I := Measurable.of_eval fun z =>
    (measurable_pi_apply _).comp ((continuous_eval_const _).measurable.comp hX.measurable)
  obtain ⟨hm,hv,hlaw⟩ := actual_conditional_filter P B U hU E hE _ hξm hξG hξz
    T hT N X hX t Y I hY hI (hind t) hinfo a ha hia
  refine ⟨hm,?_,hlaw⟩
  intro i j
  have hs := congrArg (fun Q : Matrix (Fin (d+r)) (Fin (d+r)) ℝ => Q (headIndex i) (headIndex j))
    (hcov t.val t.property)
  have ht : projIcc 0 T hT t.val=t := projIcc_of_mem hT t.property
  simp only [ht] at hs
  have he : S t.val i j=∫ w,X w t (headIndex i)*X w t (headIndex j) ∂P := by
    simpa [finiteBlocks,headIndex] using hs
  simpa only [←he] using hv i j

end Asakura.Chapter10
