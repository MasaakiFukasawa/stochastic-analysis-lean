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
theorem kalman_model_observation_information {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r : ℕ}
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
        (a w (projIcc 0 T hT s)))+ZKY w t) :
    Measurable[nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)] a ∧
      nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)=
        nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap I inferInstance) := by
  have hmc w : Continuous (fun s => a w (projIcc 0 T hT s)) :=
    (a w).continuous.comp continuous_projIcc
  let g := fun s w => C s*ᵥa w (projIcc 0 T hT s)
  have hgc w : Continuous (fun s => g s w) := by
    exact (rectangularOperatorMap.continuous.comp hC).clm_apply (hmc w)
  have hgk k w : Continuous (fun s => g s w k) := (continuous_apply k).comp (hgc w)
  have hga k s (hs : s∈Icc 0 T) : Measurable[F (realTimeClamp s)] (fun w => g s w k) := by
    have hh := (measurable_pi_apply k).comp ((rectangularOperatorMap (C s)).continuous.measurable.comp (haa ⟨s,hs⟩))
    simpa only [g,Function.comp_def,rectangularOperatorMap_apply,projIcc_of_mem hT hs] using hh
  let BV := fun k (t : HalfClosedTime) w => ∫ s in 0..(finitePrefixTime T hT t).val,g s w k
  let b := fun k s w => (Ioc (0:ℝ) T).indicator (fun s => g s w k) s
  have hdata k := stopped_continuous_drift_witness P F hF T hT (fun s w => g s w k) (hgk k) (hga k)
  have hYR w k (t : HalfClosedTime) (_ : t<⊤) : Y w (finitePrefixTime T hT t) k=
      R w (finitePrefixTime T hT t) k+BV k t w := by
    have hr := congrFun (hR w (finitePrefixTime T hT t)) k
    have hp := (ContinuousLinearMap.proj k : (Fin r → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm
      ((hgc w).intervalIntegrable (μ := volume) 0 (finitePrefixTime T hT t).val)
    change (∫ s in 0..(finitePrefixTime T hT t).val,g s w k)=
      (∫ s in 0..(finitePrefixTime T hT t).val,g s w) k at hp
    change R w (finitePrefixTime T hT t) k=Y w (finitePrefixTime T hT t) k-
      (∫ s in 0..(finitePrefixTime T hT t).val,g s w) k at hr
    rw [←hp] at hr
    dsimp only [BV]
    linarith
  have hR0 w : R w ⟨0,le_rfl,hT⟩=0 := by rw [hR,hY0,intervalIntegral.integral_same,sub_zero]
  have hrec := kalman_integral_reconstruction P F hF hle hnull c hc hcm hcT hcc T hT
    Y R I ZJY ZDI ZKY ZKR ZKDI D J K hD hJ hK hinv hI hDI hKDI hKR hKY hJY hR0
    BV (fun k => (hdata k).1) hYR b (fun k => (hdata k).2.1)
    (fun k => (hdata k).2.2.1) (fun k => (hdata k).2.2.2)
  have hKr : Continuous (fun s : ℝ => K (realTimeClamp s)) := by
    apply continuous_pi; intro i; apply continuous_pi; intro j
    exact continuous_iff_continuousAt.mpr fun s =>
      (hK i j _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  have hJr : Continuous (fun s : ℝ => J (realTimeClamp s)) := by
    apply continuous_pi; intro i; apply continuous_pi; intro j
    exact continuous_iff_continuousAt.mpr fun s =>
      (hJ i j _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  let AO := fun s => matrixOperatorMap (A s)
  let KC := fun s => matrixOperatorMap (K (realTimeClamp s)*C s)
  let JC := fun s => rectangularOperatorMap (J (realTimeClamp s)*C s)
  let CO := fun s => rectangularOperatorMap (C s)
  have hAO : Continuous AO := matrixOperatorMap.continuous.comp hA
  have hKC : Continuous KC := matrixOperatorMap.continuous.comp (hKr.matrix_mul hC)
  have hJC : Continuous JC := rectangularOperatorMap.continuous.comp (hJr.matrix_mul hC)
  have hCO : Continuous CO := rectangularOperatorMap.continuous.comp hC
  have hform : ∀ᵐ w ∂P,
      (∀ t,I w t=ZJY w t-∫ s in 0..t.val,JC s (a w (projIcc 0 T hT s))) ∧
      (∀ t,ZKDI w t=ZKY w t-∫ s in 0..t.val,KC s (a w (projIcc 0 T hT s))) ∧
      (∀ t,Y w t=(∫ s in 0..t.val,CO s (a w (projIcc 0 T hT s)))+ZDI w t) := by
    filter_upwards [hrec] with w hw
    refine ⟨?_,?_,?_⟩
    · intro t
      ext i
      have hh := (hw t).1 i
      rw [stopped_prediction_drift_integral T t.val t.property.1 t.property.2
        (fun s => J (realTimeClamp s)) C (fun s => a w (projIcc 0 T hT s)) i] at hh
      have hp := (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm
        ((hJC.clm_apply (hmc w)).intervalIntegrable (μ := volume) 0 t.val)
      change (∫ s in 0..t.val,(JC s (a w (projIcc 0 T hT s))) i)=
        (∫ s in 0..t.val,JC s (a w (projIcc 0 T hT s))) i at hp
      change I w t i=ZJY w t i-(∫ s in 0..t.val,JC s (a w (projIcc 0 T hT s))) i
      rw [←hp]
      exact hh
    · intro t
      ext i
      have hh := (hw t).2.1 i
      rw [stopped_prediction_drift_integral T t.val t.property.1 t.property.2
        (fun s => K (realTimeClamp s)) C (fun s => a w (projIcc 0 T hT s)) i] at hh
      have hp := (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm
        ((hKC.clm_apply (hmc w)).intervalIntegrable (μ := volume) 0 t.val)
      change (∫ s in 0..t.val,(KC s (a w (projIcc 0 T hT s))) i)=
        (∫ s in 0..t.val,KC s (a w (projIcc 0 T hT s))) i at hp
      change ZKDI w t i=ZKY w t i-(∫ s in 0..t.val,KC s (a w (projIcc 0 T hT s))) i
      rw [←hp]
      exact hh
    · intro t
      rw [(hw t).2.2,hR]
      change Y w t=(∫ s in 0..t.val,C s*ᵥa w (projIcc 0 T hT s))+
        (Y w t-∫ s in 0..t.val,C s*ᵥa w (projIcc 0 T hT s))
      abel
  have hmI : ∀ᵐ w ∂P,∀ t,a w t=a0+(∫ s in 0..t.val,AO s (a w (projIcc 0 T hT s)))+ZKDI w t := by
    filter_upwards [hmean,hform] with w hm hf
    exact kalman_mean_reconstruction T hT (a w) (ZKY w) (ZKDI w) a0 AO KC hAO hKC hm hf.2.1
  have hKD i j t (ht : t<⊤) : ContinuousAt (fun s => (K s*D s) i j) t := by
    change ContinuousAt (fun s => ∑ k,K s i k*D s k j) t
    exact tendsto_finset_sum _ (fun k _ => (hK i k t ht).mul (hD k j t ht))
  exact actual_integral_observation_information P F hF hle hnull c hc hcT hcc T hT
    Y I a ZKY ZKDI ZJY ZDI hYm hIm ham a0 (fun s => AO s-KC s) AO JC CO
    (hAO.sub hKC) hAO hJC hCO (fun i j s => K s i j) (fun i j s => (K s*D s) i j)
    (fun i j s => J s i j) (fun i j s => D s i j) hK hKD hJ hD hKY hJY hKDI hDI
    hmean (hform.mono (fun w hw => hw.1)) hmI (hform.mono (fun w hw => hw.2.2))

end Asakura.Chapter10
