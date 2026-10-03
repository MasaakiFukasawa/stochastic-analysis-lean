import Chapter10VectorIntegralHistory
import Chapter10ReconstructedInformation
import Chapter2FiniteTimeProjection

open MeasureTheory Set
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8 Asakura.Chapter9
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- An actual continuous matrix stochastic integral on a finite interval.
The integrator is stopped at the interval endpoint. -/
structure MatrixIntegralPathWitness {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : HalfClosedTime → MeasurableSpace Ω)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) {d r : ℕ} (T : ℝ) (hT : 0≤T)
    (Y : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (H : Fin d → Fin r → HalfClosedTime → ℝ)
    (Z : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)) : Prop where
  representation : ∃ (A M : Fin r → HalfClosedTime → Ω → ℝ)
      (N : Fin d → Fin r → HalfClosedTime → Ω → ℝ),
    (∀ j,SemimartingaleDecomposition P F
      (fun t w => Y w (finitePrefixTime T hT t) j) (A j) (M j)) ∧
    (∀ i j,SemimartingaleIntegralFormula P F c hc (A j) (M j)
      (fun z => H i j (realTimeClamp z.2)) (N i j)) ∧
    (∀ w t i,Z w t i=∑ j,N i j (realTimeClamp t.val) w)

theorem MatrixIntegralPathWitness.measurable_history {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    {d r : ℕ} (T : ℝ) (hT : 0≤T)
    (Y : Ω → C(Icc (0:ℝ) T,Fin r → ℝ)) (hYm : Measurable Y)
    (H : Fin d → Fin r → HalfClosedTime → ℝ)
    (hH : ∀ i j t,t<⊤ → ContinuousAt (H i j) t)
    (Z : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : MatrixIntegralPathWitness P F c hc T hT Y H Z) :
    Measurable[nullAugmentedInformation (m := m) P
      (MeasurableSpace.comap Y inferInstance)] Z := by
  letI : MeasurableSpace Ω := m
  let G := nullAugmentedInformation (m := m) P (MeasurableSpace.comap Y inferInstance)
  obtain ⟨A,M,N,hY,hN,hZ⟩ := @MatrixIntegralPathWitness.representation Ω m P _ F c hc d r T hT Y H Z h
  apply vector_integral_history_measurable (m := m) P F hF hle hnull
    (fun j t w => Y w (finitePrefixTime T hT t) j) A M hY H hH c hc hcT hcc N hN T hT Z hZ
    G (null_augmented_le (m := m) P _ hYm.comap_le)
    (fun E hE h0 => MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨hE,h0⟩))
  intro j s _
  have hYG : Measurable[G] Y :=
    (show Measurable[MeasurableSpace.comap Y inferInstance] Y from
      Measurable.of_comap_le le_rfl).mono (null_augmented_contains (m := m) P _) le_rfl
  exact (measurable_pi_apply j).comp ((continuous_eval_const _).measurable.comp hYG)

end Asakura.Chapter10
