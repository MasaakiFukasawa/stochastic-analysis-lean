import Chapter6ConditionalPushforwardDensity

open MeasureTheory
namespace Asakura.Chapter6
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- An invertible change of coordinates does not change the information
in the endpoint; it gives exactly p(Y)=g(Y) E[D|Y]. -/
theorem conditional_density_coordinate_change {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] (P : Measure Ω)
    (V : Ω → E) (e : E ≃ᵐ F) (D : Ω → ℝ) (q : E → ℝ) (g : F → ℝ)
    (he : P[D|MeasurableSpace.comap V inferInstance]=q ∘ V) :
    (fun w => g (e (V w))*q (e.symm (e (V w))))=
      fun w => g (e (V w))*P[D|MeasurableSpace.comap (e ∘ V) inferInstance] w := by
  have hcomap : MeasurableSpace.comap (e ∘ V) inferInstance=MeasurableSpace.comap V inferInstance := by
    rw [←MeasurableSpace.comap_comp,e.measurableEmbedding.comap_eq]
  rw [hcomap,he]
  simp only [e.symm_apply_apply,Function.comp_def]

end Asakura.Chapter6
