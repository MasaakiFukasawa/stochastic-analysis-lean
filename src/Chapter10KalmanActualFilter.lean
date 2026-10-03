import Chapter10KalmanModelInformation
import Chapter10KalmanConditionalIdentification
import Chapter10ContinuousInnovationHistory
import Chapter10KalmanIntegralReconstruction
import Chapter10ActualObservationInformation
import Chapter10KalmanReconstructionAlgebra
import Chapter10StoppedDriftWitness
import Chapter10StoppedMatrixDrift
import Chapter10RectangularOperator

open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8 Asakura.Chapter9
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- Recover equality of observation and innovation information from the
original mean equation and the actual stochastic integral definitions.
The three reconstruction identities are conclusions, not assumptions. -/
theorem kalman_actual_filter_identification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d q r : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤mΩ)
    (hnull : ∀ t E,MeasurableSet[mΩ] E → P E=0 → MeasurableSet[F t] E)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcm : Monotone c) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (T : ℝ) (hT : 0≤T) (Y R I ZJY ZDI : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (a ZKY ZKR ZKDI : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (hYm : Measurable[mΩ] Y) (hIm : Measurable[mΩ] I) (ham : Measurable[mΩ] a)
    (haa : ∀ t,Measurable[F (realTimeClamp t.val)] (fun w => a w t))
    (D J : HalfClosedTime → Matrix (Fin r) (Fin r) ℝ)
    (K : HalfClosedTime → Matrix (Fin d) (Fin r) ℝ)
    (hD : ∀ i j t,t<⊤ → ContinuousAt (fun s => D s i j) t)
    (hJ : ∀ i j t,t<⊤ → ContinuousAt (fun s => J s i j) t)
    (hK : ∀ i j t,t<⊤ → ContinuousAt (fun s => K s i j) t)
    (hinv : ∀ t,t<⊤ → D t*J t=1)
    (hI : MatrixIntegralPathWitness P F c hc T hT R (fun i j s => J s i j) I)
    (hDI : MatrixIntegralPathWitness P F c hc T hT I (fun i j s => D s i j) ZDI)
    (hKDI : MatrixIntegralPathWitness P F c hc T hT I (fun i j s => (K s*D s) i j) ZKDI)
    (hKR : MatrixIntegralPathWitness P F c hc T hT R (fun i j s => K s i j) ZKR)
    (hKY : MatrixIntegralPathWitness P F c hc T hT Y (fun i j s => K s i j) ZKY)
    (hJY : MatrixIntegralPathWitness P F c hc T hT Y (fun i j s => J s i j) ZJY)
    (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (C : ℝ → Matrix (Fin r) (Fin d) ℝ)
    (hA : Continuous A) (hC : Continuous C) (a0 : Fin d → ℝ)
    (hY0 : ∀ w,Y w ⟨0,le_rfl,hT⟩=0)
    (hR : ∀ w t,R w t=Y w t-∫ s in 0..t.val,C s*ᵥa w (projIcc 0 T hT s))
    (hmean : ∀ᵐ w ∂P,∀ t,a w t=a0+
      (∫ s in 0..t.val,(matrixOperatorMap (A s)-matrixOperatorMap (K (realTimeClamp s)*C s))
        (a w (projIcc 0 T hT s)))+ZKY w t)
    (B : BrownianSystem P (q+r))
    (S : ℝ → Matrix (Fin d) (Fin d) ℝ) (G : ℝ → Matrix (Fin d) (Fin q) ℝ)
    (hS : Continuous S) (hG : Continuous G)
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : ProbabilityTheory.HasGaussianLaw ξ P)
    (hξ0 : ∫ w,ξ w ∂P=0)
    (hinit : S 0=(fun i j => ∫ w,ξ w i*ξ w j ∂P))
    (hJinv : ∀ t,t<⊤ → J t*D t=1)
    (hSym : ∀ t∈Ico 0 T,(S t).transpose=S t)
    (hSd : ∀ t∈Ico 0 T,HasDerivWithinAt S
      (A t*S t+S t*(A t).transpose+G t*(G t).transpose-
        S t*((C t).transpose*((J (realTimeClamp t)).transpose*J (realTimeClamp t))*C t)*S t) (Ici t) t)
    (N : Fin (d+r) → Fin (q+r) → HalfClosedTime → Ω → ℝ)
    (E : Ω → C(Icc (0:ℝ) T,Fin (d+r) → ℝ))
    (hE : let K0 := fun s => S s*(C s).transpose*((J (realTimeClamp s)).transpose*J (realTimeClamp s))
      LinearStateWitness P B
        (fun s => matrixOperatorMap (finiteBlocks (A s-K0 s*C s) 0 (J (realTimeClamp s)*C s)
          (0 : Matrix (Fin r) (Fin r) ℝ)))
        (fun i j s => finiteBlocks (G s) (-(K0 s*D (realTimeClamp s)))
          (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ) i j)
        (fun w => extendZero (r := r) (ξ w)) T hT N E)
    (hIE : ∀ w t i,I w t i=E w t (tailIndex i))
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (hXE : ∀ w t i,X w t i=a w t i+E w t (headIndex i))
    (hia : ∀ i,Integrable (fun w => a w ⟨T,hT,le_rfl⟩ i) P) :
    let t : Icc (0:ℝ) T := ⟨T,hT,le_rfl⟩
    (∀ i,P[(fun w => X w t i)|nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)]=ᵐ[P]
      fun w => a w t i) ∧
    (∀ i j,P[(fun w => (X w t i-a w t i)*(X w t j-a w t j))|
      nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)]=ᵐ[P] fun _ => S T i j) ∧
    (∀ f : (Fin d → ℝ) → ℝ,Measurable f → ∀ M : ℝ,(∀ x,‖f x‖≤M) →
      P[(fun w => f (X w t))|nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)]=ᵐ[P]
        fun w => ∫ z,f (a w t+z) ∂P.map (fun w i => E w t (headIndex i))) := by
  intro t
  obtain ⟨hameas,hinfo⟩ := kalman_model_observation_information P F hF hle hnull c hc hcm hcT hcc T hT
    Y R I ZJY ZDI a ZKY ZKR ZKDI hYm hIm ham haa D J K hD hJ hK hinv
    hI hDI hKDI hKR hKY hJY A C hA hC a0 hY0 hR hmean
  have hDr : Continuous (fun s : ℝ => D (realTimeClamp s)) := by
    apply continuous_pi; intro i; apply continuous_pi; intro j
    exact continuous_iff_continuousAt.mpr fun s =>
      (hD i j _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  have hJr : Continuous (fun s : ℝ => J (realTimeClamp s)) := by
    apply continuous_pi; intro i; apply continuous_pi; intro j
    exact continuous_iff_continuousAt.mpr fun s =>
      (hJ i j _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  have hraw := continuous_innovation_history T E tailIndex t I (fun w s i => hIE w s i)
  have heq : nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)=
      nullAugmentedInformation (m := mΩ) P (pathInformation T E tailIndex t) := by
    rw [←hraw]
    exact hinfo
  have hameas' := (continuous_eval_const t).measurable.comp hameas
  obtain ⟨hm,hv,hlaw⟩ := kalman_conditional_identification P B A S G C
    (fun s => D (realTimeClamp s)) (fun s => J (realTimeClamp s)) hA hS hG hC hDr hJr
    ξ hξ hξg hξ0 T hT hinit (fun s _ => hJinv _ (half_real_time_finite s))
    (fun s _ => hinv _ (half_real_time_finite s)) hSym hSd N E hE t Y hYm heq
    (fun w => a w t) hameas' hia
  refine ⟨?_,?_,?_⟩
  · intro i
    simpa only [hXE] using hm i
  · intro i j
    simpa only [hXE,add_sub_cancel_left] using hv i j
  · intro f hf M hb
    have hx w : X w t=a w t+(fun i => E w t (headIndex i)) := funext (fun i => hXE w t i)
    simpa only [hx] using hlaw f hf M hb

end Asakura.Chapter10
