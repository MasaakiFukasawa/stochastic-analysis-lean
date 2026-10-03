import Chapter12AsianBridgeConstruction
import Mathlib.Probability.BrownianMotion.Basic

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

/-- Construct the Gaussian continuous-path input from finite-dimensional
Brownian laws and the previously proved squared path-maximum moment. -/
theorem brownian_path_gaussian_input {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (T : ℝ) (hT : 0 ≤ T)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hX : MemLp X 2 P)
    (he : ∀ w s, X w s = W ⟨s.val,s.property.1⟩ w) : HasGaussianLaw X P := by
  apply Asakura.Chapter10.gaussian_interval_path P T hT X hX
  intro n τ
  let t : Fin (n+1) → ℝ≥0 := fun i => ⟨(τ i).val,(τ i).property.1⟩
  have hg := (hW.isGaussianProcess.comp_right t).hasGaussianLaw Finset.univ
  let L : (↥(Finset.univ : Finset (Fin (n+1))) → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj ⟨i,Finset.mem_univ i⟩)
  have hl := hg.map L
  convert hl using 1
  funext w i
  exact he w (τ i)

/-- All three distributional inputs of the bridge argument are discharged
from the original Brownian motion. -/
theorem brownian_arithmetic_average_no_atom {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (x σ r T : ℝ)
    (hx : 0 < x) (hσ : 0 < σ) (hT : 0 < T)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X) (hX : MemLp X 2 P)
    (he : ∀ w s, X w s = W ⟨s.val,s.property.1⟩ w) (K : ℝ) :
    P {w | (∫ s in 0..T,x*Real.exp ((r-σ^2/2)*s+σ*X w (projIcc 0 T hT.le s)))/T = K} = 0 := by
  apply black_scholes_average_no_atom P x σ r T hx hσ hT X hXm
    (brownian_path_gaussian_input P W hW T hT.le X hX he)
  · intro s
    simp only [he]
    rw [hW.covariance_eval]
    exact min_eq_right s.property.2
  · convert hW.hasLaw_eval ⟨T,hT.le⟩ using 1
    funext w
    exact he w ⟨T,hT.le,le_rfl⟩

end Asakura.Chapter12
