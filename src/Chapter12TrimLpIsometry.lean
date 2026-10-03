import Chapter12TerminalLpEmbedding

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Passing from a smaller sigma algebra to the ambient one preserves
Hilbert-valued L2 norms and the almost-everywhere equivalence class. -/
noncomputable def trimLpIsometry {Ω E : Type*} [m : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) (mT : MeasurableSpace Ω) (hle : mT≤m) :
    Lp E 2 (P.trim hle) →ₗᵢ[ℝ] Lp E 2 P := by
  letI : MeasurableSpace Ω := m
  exact (lpMeas E ℝ mT 2 P).subtypeₗᵢ.comp
    (lpMeasToLpTrimLie E ℝ 2 P hle).symm.toLinearIsometry

theorem trimLpIsometry_coe {Ω E : Type*} [m : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) (mT : MeasurableSpace Ω) (hle : mT≤m)
    (U : Lp E 2 (P.trim hle)) :
    (@trimLpIsometry Ω E m _ _ _ P mT hle U : Ω → E)=ᵐ[P] (U : Ω → E) := by
  letI : MeasurableSpace Ω := m
  exact lpTrimToLpMeas_ae_eq (𝕜:=ℝ) hle U

end Asakura.Chapter12
