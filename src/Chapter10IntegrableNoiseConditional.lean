import Chapter10IntegrableBracketConditional
import Chapter7VectorIntegralCovariances

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Deterministic Wiener integrals with merely locally integrable products
have Gaussian laws. In particular, fixed-time stopping is allowed. -/
theorem integrable_deterministic_noise_conditional_characteristic {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (B : BrownianSystem P n)
    (H : Fin n → ℝ → ℝ) (hHm : ∀ j,Measurable (H j))
    (hi : ∀ j b,0≤b → IntervalIntegrable (H j) volume 0 b)
    (hpi : ∀ i j b,0≤b → IntervalIntegrable (fun s => H i s*H j s) volume 0 b)
    (N : Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ j,LocalMProcessWitness P B.F (N j))
    (hNI : ∀ j,ItoCovarianceFormula P B.F (B.W j) (fun z => H j z.2) (N j))
    (R : ℝ) (hR : 0≤R) (u : ℝ) :
    P[(fun w => Complex.exp ((u:ℂ)*((∑ j,N j (realTimeClamp R) w:ℝ):ℂ)*Complex.I)) | B.F ⊥]=ᵐ[P]
      fun _ => Complex.exp (-((∫ s in 0..R,∑ j,(H j s)^2:ℝ):ℂ)*(u:ℂ)^2/2) := by
  obtain ⟨hZ,C,_,hC,_,hCe,_⟩ := locally_integrable_vector_covariances P B (fun j z => H j z.2)
    (fun j => (hHm j).comp measurable_snd) (fun j _ b hb => hi j b hb)
    (fun i j _ b hb => hpi i j b hb) N hN hNI
  have hf b (hb : 0≤b) : IntervalIntegrable (fun s => ∑ j,(H j s)^2) volume 0 b := by
    have hh := IntervalIntegrable.sum Finset.univ (fun j _ => hpi j j b hb)
    have he : (∑ j : Fin n, fun s => H j s * H j s) = (fun s => ∑ j, (H j s)^2) := by
      funext s
      simp only [Finset.sum_apply, pow_two]
    rw [he] at hh
    exact hh
  exact integrable_deterministic_bracket_conditional_characteristic P B.F B.mono B.le B.null _ C hZ hC
    (fun s => ∑ j,(H j s)^2) hf (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hCe R hR u

end Asakura.Chapter10
