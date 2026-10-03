import Chapter10LinearForcedExistence
import Chapter8BrownianForcingPath
import Chapter3ContinuousIntegralConstruction

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Construct the deterministic-coefficient Ito integrals and then the linear
state equation. The forcing in the equation is the constructed Ito integral,
not an assumed Gaussian process. -/
theorem time_dependent_linear_sde_family {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (T : ℝ) (hT : 0≤T) :
    ∃ (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
      (X : (Fin d → ℝ) → ℝ → Ω → (Fin d → ℝ)),
      (∀ i j,LocalMProcessWitness P B.F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j)) ∧
      (∀ t,Measurable (fun p : (Fin d → ℝ) × Ω => X p.1 t p.2)) ∧
      (∀ x w,Continuous (fun t => X x t w)) ∧
      ∀ x w t,t∈Icc 0 T →
        X x t w=x+(∫ s in 0..t,A s (X x s w))+(fun i => ∑ j,N i j (realTimeClamp t) w) := by
  have hex i j := continuous_adapted_ito_exists P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W j) (B.martingale j) (fun z => G i j z.2)
    (fun r _ _ => (show Measurable[B.F (realTimeClamp r)] (fun _ : Ω => G i j r) from measurable_const))
    (fun _ _ _ _ => (hG i j).continuousOn)
  choose N hN hNI using hex
  let W := fun t w i => ∑ j,N i j (realTimeClamp t) w
  have hWm t : Measurable (W t) := Measurable.of_eval (fun i =>
    Finset.measurable_sum _ (fun j _ =>
      ((hN i j).adapted P B.F _ (half_real_time_finite t)).mono (B.le _) le_rfl))
  have hWc w : Continuous (fun t => W t w) := by
    apply continuous_pi
    intro i
    apply continuous_finset_sum
    intro j _
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hN i j).path P B.F w _ (half_real_time_finite t)).comp real_time_clamp_continuous.continuousAt
  obtain ⟨X,hm,hc,he⟩ := continuous_linear_forced_family A hA W hWm hWc T hT
  exact ⟨N,X,hN,hNI,hm,hc,he⟩

end Asakura.Chapter10
