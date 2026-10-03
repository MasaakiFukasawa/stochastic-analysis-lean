import Chapter9BoundedTests

open MeasureTheory
namespace Asakura.Chapter9
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem integral_pair_conditional {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (U V : Ω → ℝ) (hU : Integrable U P) (hV : StronglyMeasurable[G] V)
    (C : ℝ) (hC : ∀ w,‖V w‖≤C) :
    (∫ w,V w*U w ∂P)=(∫ w,V w*P[U|G] w ∂P) := by
  have hp := condExp_stronglyMeasurable_mul_of_bound hG hV hU C (ae_of_all _ hC)
  have he := integral_congr_ae hp
  rw [integral_condExp hG] at he
  exact he

/-- A future test with present-state conditional mean cannot distinguish a
past variable from its conditional mean given the present state. -/
theorem future_test_regression_pairing {Ω E : Type*} [m : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : MeasurableSpace Ω) (hF : F≤m)
    (X : Ω → E) (hX : Measurable[F] X) (Y Z V : Ω → ℝ)
    (hY : @IsBoundedBorel Ω m Y) (hZ : @IsBoundedBorel Ω m Z) (hV : Integrable V P)
    (hYF : Measurable[F] Y) (hZF : Measurable[F] Z)
    (hreg : P[Y|MeasurableSpace.comap X inferInstance]=ᵐ[P] Z)
    (g : E → ℝ) (hg : IsBoundedBorel g)
    (hfuture : P[V|F]=ᵐ[P] (fun w => g (X w))) :
    (∫ w,Y w*V w ∂P)=(∫ w,Z w*V w ∂P) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨CY,_,hCY⟩ := hY.2
  obtain ⟨CZ,_,hCZ⟩ := hZ.2
  obtain ⟨Cg,_,hCg⟩ := hg.2
  have hGX : Measurable[MeasurableSpace.comap X inferInstance] (fun w => g (X w)) :=
    hg.1.comp (comap_measurable X)
  calc
    _ = ∫ w,Y w*P[V|F] w ∂P := integral_pair_conditional P F hF V Y hV hYF.stronglyMeasurable CY hCY
    _ = ∫ w,g (X w)*Y w ∂P := by
      apply integral_congr_ae
      filter_upwards [hfuture] with w hw
      rw [hw,mul_comm]
    _ = ∫ w,g (X w)*P[Y|MeasurableSpace.comap X inferInstance] w ∂P :=
      integral_pair_conditional P _ (hX.comap_le.trans hF) Y _ (hY.integrable P)
        hGX.stronglyMeasurable Cg (fun w => hCg (X w))
    _ = ∫ w,Z w*g (X w) ∂P := by
      apply integral_congr_ae
      filter_upwards [hreg] with w hw
      rw [hw,mul_comm]
    _ = ∫ w,Z w*P[V|F] w ∂P := integral_congr_ae (hfuture.symm.mono (fun w hw => congrArg (fun a => Z w*a) hw))
    _ = _ := (integral_pair_conditional P F hF V Z hV hZF.stronglyMeasurable CZ hCZ).symm
end Asakura.Chapter9
