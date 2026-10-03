import Chapter12ProbabilityTrim

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

noncomputable def terminalLpEmbedding {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (mT : MeasurableSpace Ω) (hle : mT ≤ m) :
    Lp ℝ 2 (P.trim hle) →L[ℝ] Lp ℝ 2 P := by
  letI : MeasurableSpace Ω := m
  exact (lpMeas ℝ ℝ mT 2 P).subtypeL.comp
    (lpMeasToLpTrimLie ℝ ℝ 2 P hle).symm.toLinearIsometry.toContinuousLinearMap

theorem terminalLpEmbedding_coe {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (U : Lp ℝ 2 (P.trim hle)) :
    (@terminalLpEmbedding Ω m P mT hle U : Ω → ℝ) =ᵐ[P] (U : Ω → ℝ) :=
  by
    letI : MeasurableSpace Ω := m
    exact lpTrimToLpMeas_ae_eq (𝕜 := ℝ) hle U

theorem terminalLpEmbedding_integral {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (U : Lp ℝ 2 (P.trim hle)) :
    (∫ w,@terminalLpEmbedding Ω m P mT hle U w ∂P)=∫ w,U w ∂P.trim hle := by
  letI : MeasurableSpace Ω := m
  exact (integral_congr_ae (@terminalLpEmbedding_coe Ω m P mT hle U)).trans
    (integral_trim hle (Lp.stronglyMeasurable U))

end Asakura.Chapter12
