import Chapter10CompletedConditionalLaw
import Chapter10ContinuousStateLaw
import Chapter10FiniteBlockProjection

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter9
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Identify the conditional mean, covariance and entire conditional law from
an actual centered linear state, with the Gaussianity and centering proved
from its stochastic equation. The history independence is supplied by the
Kalman covariance cancellation theorem. -/
theorem actual_conditional_filter {Ω U V : Type*} [m : MeasurableSpace Ω]
    [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin (d+r) → ℝ) →L[ℝ] (Fin (d+r) → ℝ)) (hA : Continuous A)
    (G : Fin (d+r) → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin (d+r) → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (hξ0 : ∫ w,ξ w ∂P=0) (T : ℝ) (hT : 0≤T)
    (N : Fin (d+r) → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin (d+r) → ℝ))
    (hX : LinearStateWitness P B A G ξ T hT N X)
    (t : Icc (0:ℝ) T) (Y : Ω → U) (I : Ω → V)
    (hY : Measurable Y) (hI : Measurable I)
    (hind : IndepFun (fun w (i : Fin d) => X w t (headIndex i)) I P)
    (hinfo : nullAugmentedInformation (m := m) P (MeasurableSpace.comap Y inferInstance)=
      nullAugmentedInformation (m := m) P (MeasurableSpace.comap I inferInstance))
    (a : Ω → Fin d → ℝ)
    (ha : Measurable[nullAugmentedInformation (m := m) P (MeasurableSpace.comap Y inferInstance)] a)
    (hia : ∀ i,Integrable (fun w => a w i) P) :
    let e := fun w (i : Fin d) => X w t (headIndex i)
    let H := nullAugmentedInformation (m := m) P (MeasurableSpace.comap Y inferInstance)
    letI : MeasurableSpace Ω := m
    (∀ i,P[(fun w => a w i+e w i)|H]=ᵐ[P] (fun w => a w i)) ∧
    (∀ i j,P[(fun w => e w i*e w j)|H]=ᵐ[P] (fun _ => ∫ w,e w i*e w j ∂P)) ∧
    (∀ f : (Fin d → ℝ) → ℝ,Measurable f → ∀ C : ℝ,(∀ x,‖f x‖≤C) →
      P[(fun w => f (a w+e w))|H]=ᵐ[P] fun w => ∫ z,f (a w+z) ∂P.map e) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨hg,hmean⟩ := hX.centered_gaussian P B A hA G hG ξ hξ hξg hξ0 T hT N X
  let e := fun w (i : Fin d) => X w t (headIndex i)
  have he : Measurable e := Measurable.of_eval fun i =>
    (measurable_pi_apply _).comp ((continuous_eval_const t).measurable.comp hX.measurable)
  have heg : HasGaussianLaw e P := by
    exact hg.map ((coordinateProjection headIndex).comp (ContinuousMap.evalCLM ℝ t))
  have hz i : (∫ w,e w i ∂P)=0 := by
    have hi := (hg.map (ContinuousMap.evalCLM ℝ t)).integrable
    have hh := (show (Fin (d+r) → ℝ) →L[ℝ] ℝ from
      ContinuousLinearMap.proj (headIndex i)).integral_comp_comm hi
    change (∫ w,e w i ∂P)=(∫ w,X w t ∂P) (headIndex i) at hh
    rw [hh,hmean]
    rfl
  obtain ⟨hm,hcov,_⟩ := completed_filter_identification P Y I hY hI e a he heg hind hinfo ha hia hz
  refine ⟨hm,hcov,?_⟩
  intro f hf C hb
  exact completed_state_conditional_law P Y I hY hI e a he hind hinfo ha f hf C hb

end Asakura.Chapter10
