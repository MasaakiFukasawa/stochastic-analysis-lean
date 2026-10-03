import Chapter12FutureDirections
import Chapter12WienerPastRepresentatives

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- Future parts of arbitrary deterministic Wiener directions are independent
of all past Brownian coordinates, including an uncountable time index. -/
theorem finite_future_independent_past {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T a : ℝ)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ)
    (hm : ∀ z,Measurable (X z))
    (he : ∀ z,X z =ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (n : ℕ) (u : Fin n → FiniteWienerHilbert d T) :
    IndepFun (fun w i => W (finiteFuturePart T a (u i)) w)
      (fun w (z : {z : BrownianTimeCoordinates d T // z.2.val≤a}) => X z.val w) P := by
  apply wiener_future_independent_past_representatives P W hlaw n
    (fun i => finiteFuturePart T a (u i))
    (fun z : {z : BrownianTimeCoordinates d T // z.2.val≤a} => brownianTimeDirection z.val)
    _ (fun z => hm z.val) (fun z => he z.val)
  intro i z
  exact finite_future_part_past_orthogonal T a (u i) z.val z.property

end Asakura.Chapter12
