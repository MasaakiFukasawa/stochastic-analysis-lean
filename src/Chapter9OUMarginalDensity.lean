import Chapter9OUTwoTimeDensity
import Chapter9OUTransitionBounded

open MeasureTheory Matrix
open scoped NNReal ENNReal
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The marginal density at any later time follows from the actual two-time
law. It can be computed from the law at any earlier time. -/
theorem standard_ou_marginal_from_time {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (s t : ℝ) (hs : 0≤s) (hst : s<t)
 :
    let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
    P.map (X t)=volume.withDensity (fun y => ENNReal.ofReal
      (∫ x,gaussianKernel (Real.exp (-(t-s))) (1-Real.exp (-2*(t-s))) x y ∂P.map (X s))) := by
  let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
  have hXs := (standard_ou_adapted P B N hN ξ hξ s).mono (B.le _) le_rfl
  have hXt := (standard_ou_adapted P B N hN ξ hξ t).mono (B.le _) le_rfl
  let μ := P.map (X s)
  haveI : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hXs.aemeasurable).mpr inferInstance
  let v : ℝ≥0 := ⟨1-Real.exp (-2*(t-s)),(ou_variance_positive (t-s) (sub_pos.mpr hst)).le⟩
  have hv : v≠0 := by
    intro he
    exact (ou_variance_positive (t-s) (sub_pos.mpr hst)).ne' (congrArg (fun z : ℝ≥0 => (z:ℝ)) he)
  have he := congrArg (fun Q => Q.map (Prod.snd : (Fin d → ℝ) × (Fin d → ℝ) → (Fin d → ℝ)))
    (standard_ou_two_time_density P B N hN hNI ξ hξ s t hs hst)
  rw [Measure.map_map measurable_snd (hXs.prodMk hXt)] at he
  change P.map (X t)=((μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel (Real.exp (-(t-s))) v z.1 z.2))).map Prod.snd at he
  rw [gaussian_mixture_marginal μ (Real.exp (-(t-s))) v hv] at he
  exact he
end Asakura.Chapter9
