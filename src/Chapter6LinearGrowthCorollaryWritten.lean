import Chapter6LinearGrowthPositiveDensityWritten
import Chapter6AffineLinearGrowth

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators ENNReal NNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The complete linear-growth density corollary with the original
coefficient assumption, rather than an assumed transformed growth bound. -/
theorem linear_growth_density_corollary_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ)
    (μ : ℝ × (Fin d → ℝ) → Fin d → ℝ) (hμ : Continuous μ)
    (R : ℝ) (hR : 0<R) (M : ℝ) (hM : 0≤M)
    (hμM : ∀ z,‖WithLp.toLp 2 (μ z)‖≤M*(1+‖WithLp.toLp 2 z.2‖)) :
    let b := fun z : ℝ × (Fin d → ℝ) => L.symm (μ (z.1,x+L z.2))
    let H := stoppedBrownianCoefficient P B b R hR.le
    let Y := fun w => x+L (fun i => B.W i (realTimeClamp R) w)
    let g := gaussianAffineDensity L x ⟨R,hR.le⟩
    ∃ K : ℝ,0≤K ∧ ∃ (N : Fin d → HalfClosedTime → Ω → ℝ) (C : HalfClosedTime → Ω → ℝ)
      (Q : Measure Ω) (p : (Fin d → ℝ) → ℝ),IsProbabilityMeasure Q ∧
      (∀ j,LocalMProcessWitness P B.F (N j)) ∧
      (∀ j,ItoCovarianceFormula P B.F (B.W j) (fun z => H j (realTimeClamp z.2) z.1) (N j)) ∧
      (∀ r,0≤r → C (realTimeClamp r)=ᵐ[P] fun w => ∫ s in 0..r,∑ j,(H j (realTimeClamp s) w)^2) ∧
      Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp ((∑ j,N j (realTimeClamp R) w)-C (realTimeClamp R) w/2))) ∧
      P.map Y=volume.withDensity (fun y => ENNReal.ofReal (g y)) ∧
      Q.map Y=volume.withDensity (fun y => ENNReal.ofReal (p y)) ∧
      ((fun w => p (Y w))=fun w => g (Y w)*P[(fun w => Real.exp ((∑ j,N j (realTimeClamp R) w)-C (realTimeClamp R) w/2))|MeasurableSpace.comap Y inferInstance] w) ∧
      (∀ᵐ y ∂(volume : Measure (Fin d → ℝ)),
        g y*Real.exp (-linearGrowthDensityConstant d K R*(1+‖WithLp.toLp 2 (L.symm (y-x))‖^2))≤p y) ∧
      (∀ p' : (Fin d → ℝ) → ℝ,Continuous p' → p'=ᵐ[volume] p → ∀ y,0<p' y) := by
  obtain ⟨K,hK,hKb⟩ := affine_transformed_linear_growth L x μ M hM hμM
  exact ⟨K,hK,linear_growth_positive_density_written P B L x μ hμ R hR K hK hKb⟩

end Asakura.Chapter6
