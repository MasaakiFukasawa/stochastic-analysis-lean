import Chapter12FiniteFutureIndependence
import Chapter12IndependentConditionalIntegral

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

/-- Conditional expectation is obtained by integrating the future Gaussian
vector against its actual law, with all past coordinates held fixed. -/
theorem finite_future_conditional_integral {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T a : ℝ)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ)
    (hm : ∀ z,Measurable (X z))
    (he : ∀ z,X z =ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (n : ℕ) (u : Fin n → FiniteWienerHilbert d T)
    (f : (({z : BrownianTimeCoordinates d T // z.2.val≤a} → ℝ) × (Fin n → ℝ)) → ℝ)
    (hfm : Measurable f)
    (hf : Integrable f ((P.map (fun w (z : {z : BrownianTimeCoordinates d T // z.2.val≤a}) => X z.val w)).prod
      (P.map (fun w i => W (finiteFuturePart T a (u i)) w)))) :
    let past := fun w (z : {z : BrownianTimeCoordinates d T // z.2.val≤a}) => X z.val w
    let future := fun w i => W (finiteFuturePart T a (u i)) w
    HasGaussianLaw future P ∧
    P[(fun w => f (past w,future w))|MeasurableSpace.comap past inferInstance] =ᵐ[P]
      (fun w => ∫ y,f (past w,y) ∂(P.map future)) := by
  letI : MeasurableSpace Ω := m
  dsimp only
  have hp : Measurable (fun w (z : {z : BrownianTimeCoordinates d T // z.2.val≤a}) => X z.val w) :=
    Measurable.of_eval (fun z => hm z.val)
  have hq : Measurable (fun w i => W (finiteFuturePart T a (u i)) w) :=
    Measurable.of_eval (fun i => (Lp.stronglyMeasurable _).measurable)
  constructor
  · exact wiener_joint_gaussian P W hlaw _
  · exact independent_conditional_integral P _ _ _ _ hp hq
      (hasLaw_map hp.aemeasurable) (hasLaw_map hq.aemeasurable)
      (finite_future_independent_past P T a W hlaw X hm he n u).symm f hfm hf

end Asakura.Chapter12
