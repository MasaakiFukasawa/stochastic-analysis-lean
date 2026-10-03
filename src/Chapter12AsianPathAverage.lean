import Chapter12AsianMonotonicity
import Chapter12ContinuousPathSigma
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable def asianBridgeAverage (x σ r T : ℝ) (hT : 0 ≤ T)
    (w : C(Icc (0:ℝ) T,ℝ) × ℝ) : ℝ :=
  (∫ s in 0..T, x*Real.exp ((r-σ^2/2)*s+σ*w.1 (projIcc 0 T hT s)+σ*s/T*w.2))/T

theorem asianBridgeAverage_measurable (x σ r T : ℝ) (hT : 0 ≤ T) :
    Measurable (asianBridgeAverage x σ r T hT) := by
  let f := fun w : (C(Icc (0:ℝ) T,ℝ) × ℝ) × ℝ =>
    x*Real.exp ((r-σ^2/2)*w.2+σ*w.1.1 (projIcc 0 T hT w.2)+σ*w.2/T*w.1.2)
  have hf : Continuous f := by unfold f; fun_prop
  have hm := (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 T))).measurable
  have he : asianBridgeAverage x σ r T hT =
      (fun w => (∫ s, f (w,s) ∂volume.restrict (Ioc 0 T))/T) := by
    funext w
    unfold asianBridgeAverage
    rw [intervalIntegral.integral_of_le hT]
  rw [he]
  exact hm.div_const T

theorem asianBridgeAverage_strictMono (x σ r T : ℝ)
    (hx : 0 < x) (hσ : 0 < σ) (hT : 0 < T) (b : C(Icc (0:ℝ) T,ℝ)) :
    StrictMono (fun z => asianBridgeAverage x σ r T hT.le (b,z)) := by
  exact asian_average_strictMono x σ T hx hσ hT
    (fun s => (r-σ^2/2)*s+σ*b (projIcc 0 T hT.le s)) (by fun_prop)

/-- The complete atomlessness argument for the arithmetic average, once the
Brownian path law is supplied: bridge independence, a strictly monotone
terminal coordinate, and integration over the product law. -/
theorem asian_average_no_atom {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x σ r T : ℝ)
    (hx : 0 < x) (hσ : 0 < σ) (hT : 0 < T)
    (X B : Ω → C(Icc (0:ℝ) T,ℝ))
    (hXm : Measurable X) (hBm : Measurable B) (hXg : HasGaussianLaw X P)
    (hcov : ∀ s : Icc (0:ℝ) T,
      cov[(fun w => X w ⟨T,hT.le,le_rfl⟩),(fun w => X w s); P] = s.val)
    (hB : ∀ w s, B w s = X w s-s.val/T*X w ⟨T,hT.le,le_rfl⟩)
    (hterminal : HasLaw (fun w => X w ⟨T,hT.le,le_rfl⟩) (gaussianReal 0 ⟨T,hT.le⟩) P)
    (K : ℝ) :
    P {w | asianBridgeAverage x σ r T hT.le (B w,X w ⟨T,hT.le,le_rfl⟩) = K} = 0 := by
  have hn : (⟨T,hT.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have he := congrArg NNReal.toReal h
    exact hT.ne' he
  letI := nullSingletonClass_gaussianReal (μ := 0) hn
  letI : IsProbabilityMeasure (P.map B) := (Measure.isProbabilityMeasure_map_iff hBm.aemeasurable).mpr inferInstance
  have hi := bridge_path_terminal_independent P T hT X B hXm hXg hcov hB
  have hl := hi.hasLaw_prod (hasLaw_map hBm.aemeasurable) hterminal
  exact no_atom_from_bridge_terminal_law P (P.map B) (gaussianReal 0 ⟨T,hT.le⟩)
    _ hl (asianBridgeAverage x σ r T hT.le) (asianBridgeAverage_measurable x σ r T hT.le)
    (asianBridgeAverage_strictMono x σ r T hx hσ hT) K

end Asakura.Chapter12
