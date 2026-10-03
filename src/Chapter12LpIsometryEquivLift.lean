import Chapter12LpIsometryLift

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

noncomputable def lpIsometryEquivLift {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : Measure Ω) (p : ℝ≥0∞) [Fact (1≤p)] (J : E ≃ₗᵢ[ℝ] F) :
    Lp E p P ≃ₗᵢ[ℝ] Lp F p P :=
  LinearIsometryEquiv.ofSurjective (lpIsometryLift P p J.toLinearIsometry) (by
    intro f
    refine ⟨lpIsometryLift P p J.symm.toLinearIsometry f,?_⟩
    apply Lp.ext
    filter_upwards [J.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
      (lpIsometryLift P p J.symm.toLinearIsometry f),
      J.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f] with w h1 h2
    change J.toContinuousLinearEquiv.toContinuousLinearMap.compLp
      (J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp f) w=f w
    change J.toContinuousLinearEquiv.toContinuousLinearMap.compLp
      (J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp f) w=
      J (J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp f w) at h1
    rw [h1,h2]
    exact J.apply_symm_apply _)

end Asakura.Chapter12
