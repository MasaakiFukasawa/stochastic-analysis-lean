import Chapter6LikelihoodPushforward
import Chapter6LikelihoodQuadratic

open MeasureTheory Set Filter Matrix
open scoped ENNReal BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

local instance (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))

/-- A single finite collection of path functionals defines the whole
likelihood family, with one exceptional set valid for every parameter. -/
theorem common_likelihood_family {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) {n : ℕ} (X : Ω → E) (hX : Measurable X)
    (I : Ω → Matrix (Fin n) (Fin n) ℝ) (b : Ω → Fin n → ℝ)
    (J : E → Matrix (Fin n) (Fin n) ℝ) (a : E → Fin n → ℝ)
    (hJ : Measurable J) (ha : Measurable a)
    (hI : I=ᵐ[P] J ∘ X) (hb : b=ᵐ[P] a ∘ X) :
    let L := fun θ y => ENNReal.ofReal (Real.exp (quadraticLogLikelihood (J y) (a y) θ))
    (∀ θ,Measurable (L θ)) ∧
    (∀ᵐ w ∂P,∀ θ,ENNReal.ofReal (Real.exp (quadraticLogLikelihood (I w) (b w) θ))=L θ (X w)) ∧
    (∀ θ,(P.withDensity (fun w => ENNReal.ofReal (Real.exp (quadraticLogLikelihood (I w) (b w) θ)))).map X=
      (P.map X).withDensity (L θ)) ∧
    (∀ y,(J y).PosDef → ∀ θ,
      quadraticLogLikelihood (J y) (a y) θ≤quadraticLogLikelihood (J y) (a y) ((J y)⁻¹ *ᵥ a y)) := by
  classical
  let L := fun θ y => ENNReal.ofReal (Real.exp (quadraticLogLikelihood (J y) (a y) θ))
  have hm θ : Measurable (L θ) := by
    have hb i : Measurable (fun y => a y i) := (measurable_pi_apply i).comp ha
    have hI i j : Measurable (fun y => J y i j) := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hJ)
    apply Measurable.ennreal_ofReal
    apply Measurable.exp
    unfold quadraticLogLikelihood dotProduct Matrix.mulVec
    exact (Finset.measurable_sum _ (fun i _ => (hb i).const_mul _)).sub
      ((Finset.measurable_sum _ (fun i _ => (Finset.measurable_sum _ (fun j _ => (hI i j).mul_const _)).const_mul _)).div_const 2)
  have hall : ∀ᵐ w ∂P,∀ θ,ENNReal.ofReal (Real.exp (quadraticLogLikelihood (I w) (b w) θ))=L θ (X w) := by
    filter_upwards [hI,hb] with w hi hb
    intro θ
    dsimp [L]
    rw [hi,hb]
    rfl
  refine ⟨hm,hall,?_,?_⟩
  · intro θ
    have he := withDensity_congr_ae (μ := P) (hall.mono (fun w hw => hw θ))
    rw [he]
    exact likelihood_pushforward P X hX (L θ) (hm θ)
  · intro y hy
    exact (quadratic_likelihood_unique_maximum (J y) hy (a y)).1

end Asakura.Chapter6
