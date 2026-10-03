import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- A deterministic Hilbert isometry induces an isometry of random fields. -/
noncomputable def lpIsometryLift {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : Measure Ω) (p : ℝ≥0∞) [Fact (1≤p)] (J : E →ₗᵢ[ℝ] F) :
    Lp E p P →ₗᵢ[ℝ] Lp F p P where
  toLinearMap := J.toContinuousLinearMap.compLpₗ p P
  norm_map' f := by
    rw [Lp.norm_def,Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [J.toContinuousLinearMap.coeFn_compLp f] with w hw
    change ‖J.toContinuousLinearMap.compLp f w‖=‖f w‖
    rw [hw]
    exact J.norm_map _

end Asakura.Chapter12
