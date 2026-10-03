import Chapter12ContinuousPathPrimitive
import Chapter12PathVolterraBijection

open MeasureTheory Set
open scoped Topology NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem volterra_linear_bijective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0≤T) (A : C(Icc (0:ℝ) T,E →L[ℝ] E)) :
    Function.Bijective ((ContinuousLinearMap.id ℝ C(Icc (0:ℝ) T,E))-
      (pathPrimitive T hT).comp (continuousMapApply A)) := by
  let b := fun t x => A (projIcc 0 T hT t) x
  have hc : Continuous (Function.uncurry b) :=
    (A.continuous.comp (continuous_projIcc.comp continuous_fst)).clm_apply continuous_snd
  have hl t : LipschitzWith ‖A‖₊ (b t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    dsimp only [b]
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact ((A _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm _) (norm_nonneg _))
  exact volterra_path_bijective T hT b ‖A‖₊ hc hl _ (fun _ _ => rfl)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.volterra_linear_bijective
