import Chapter9OUConditionalTransition
import Chapter9GaussianBoundedTransition

open MeasureTheory Matrix
open scoped NNReal
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false

 theorem standard_ou_adapted {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (s : ℝ) :
    Measurable[B.F (realTimeClamp s)]
      (fun w i => Real.exp (-s)*(ξ w i+∑ j,N i j (realTimeClamp s) w)) := by
  letI : MeasurableSpace Ω := B.F (realTimeClamp s)
  apply measurable_pi_lambda
  intro i
  exact measurable_const.mul (((measurable_pi_apply i).comp (hξ.mono (B.mono bot_le) le_rfl)).add
    (Finset.measurable_sum _ (fun j _ => (hN i j).adapted P B.F _ (half_real_time_finite s))))

/-- The bounded-Borel forward Markov property used in the finite-cylinder
reversal lemma follows from the constructed OU stochastic integrals. -/
theorem standard_ou_bounded_transition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (s t : ℝ) (hs : 0≤s) (hst : s≤t)
    (f : (Fin d → ℝ) → ℝ) (hf : IsBoundedBorel f) :
    let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
    ∃ g : (Fin d → ℝ) → ℝ,IsBoundedBorel g ∧
      P[(fun w => f (X t w))|B.F (realTimeClamp s)]=ᵐ[P] (fun w => g (X s w)) := by
  dsimp only
  rcases eq_or_lt_of_le hst with he|hlt
  · subst t
    refine ⟨f,hf,?_⟩
    have hm := hf.1.comp (standard_ou_adapted P B N hN ξ hξ s)
    have hi : Integrable (fun w => f (fun i => Real.exp (-s)*(ξ w i+∑ j,N i j (realTimeClamp s) w))) P :=
      (hf.comp _ ((standard_ou_adapted P B N hN ξ hξ s).mono (B.le _) le_rfl)).integrable P
    have he := condExp_of_stronglyMeasurable (B.le _) hm.stronglyMeasurable hi
    dsimp only [Function.comp_def] at he
    rw [he]
  · let v : ℝ≥0 := ⟨1-Real.exp (-2*(t-s)),(ou_variance_positive (t-s) (sub_pos.mpr hlt)).le⟩
    have hv : v≠0 := by
      intro he
      exact (ou_variance_positive (t-s) (sub_pos.mpr hlt)).ne' (congrArg (fun z : ℝ≥0 => (z:ℝ)) he)
    refine ⟨fun x => ∫ y,gaussianKernel (Real.exp (-(t-s))) v x y*f y,
      gaussian_transition_bounded_borel _ v hv f hf,?_⟩
    obtain ⟨C,_,hC⟩ := hf.2
    exact standard_ou_conditional_transition P B N hN hNI ξ hξ s t hs hlt f hf.1 C hC
end Asakura.Chapter9
