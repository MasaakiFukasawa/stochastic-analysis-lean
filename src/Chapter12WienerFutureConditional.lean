import Chapter12IndependentSigmaIntegrable
import Chapter12FutureCompletedIndependence
import Chapter12WienerFutureAverage

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- The constructed future average is the conditional expectation given
the whole completed Brownian past. Integrability is assumed only for the
original cylinder random variable. -/
theorem wiener_future_conditional_expectation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (T a : ℝ) (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ) (hm : ∀ z,Measurable (X z))
    (he : ∀ z,X z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (hF : B.F (realTimeClamp a)=Asakura.nullAugmentation (m := m) P
      (MeasurableSpace.comap (fun w (z : {z : BrownianTimeCoordinates d T // z.2.val≤a}) => X z.val w) inferInstance))
    (n : ℕ) (u : Fin n → FiniteWienerHilbert d T)
    (N : Fin n → HalfClosedTime → Ω → ℝ) (hN : ∀ i,ContinuousM2Witness P B.F (N i))
    (hterm : ∀ i,(W (u i) : Ω → ℝ)=ᵐ[P] N i ⊤)
    (hfuture : (fun w i => W (finiteFuturePart T a (u i)) w)=ᵐ[P]
      fun w i => N i ⊤ w-N i (realTimeClamp a) w)
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f)
    (hi : Integrable (fun w => f (fun i => W (u i) w)) P) :
    P[(fun w => f (fun i => W (u i) w))|B.F (realTimeClamp a)]=ᵐ[P]
      (fun w => ∫ y,f ((fun i => N i (realTimeClamp a) w)+y)
        ∂(P.map (fun v i => W (finiteFuturePart T a (u i)) v))) := by
  let Y := fun w i => W (finiteFuturePart T a (u i)) w
  have hYm : Measurable Y := measurable_pi_iff.mpr (fun i => (Lp.stronglyMeasurable _).measurable)
  have hind : Indep (MeasurableSpace.comap Y inferInstance) (B.F (realTimeClamp a)) P := by
    rw [hF]
    exact finite_future_independent_completed_past P T a W hlaw X hm he n u
  let g := fun z : Ω × (Fin n → ℝ) => f ((fun i => N i (realTimeClamp a) z.1)+z.2)
  have hg : @Measurable _ _ ((B.F (realTimeClamp a)).prod inferInstance) inferInstance g := by
    letI : MeasurableSpace Ω := B.F (realTimeClamp a)
    exact hf.comp ((measurable_pi_iff.mpr (fun i => ((hN i).adapted _).comp measurable_fst)).add measurable_snd)
  have heq : (fun w => g (w,Y w))=ᵐ[P] (fun w => f (fun i => W (u i) w)) := by
    filter_upwards [ae_all_iff.mpr hterm,hfuture] with w ht hu
    apply congrArg f
    funext i
    have hui := congrFun hu i
    dsimp only [g,Y,Pi.add_apply]
    rw [hui,ht i]
    ring
  letI : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hYm.aemeasurable).mpr inferInstance
  have hcond := independent_sigma_integral_of_integrable P (B.F (realTimeClamp a)) (B.le _)
    Y hYm (P.map Y) (hasLaw_map hYm.aemeasurable) hind g hg (hi.congr heq.symm)
  exact (condExp_congr_ae (m := B.F (realTimeClamp a)) heq.symm).trans hcond

end Asakura.Chapter12
#print axioms Asakura.Chapter12.wiener_future_conditional_expectation
