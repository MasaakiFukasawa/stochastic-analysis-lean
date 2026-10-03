import Chapter12DerivativeGrowthBilinear
import Chapter12LinearCylinder

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem scalar_vector_map_smooth (H:Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :
    ContDiff ℝ ∞ (fun x:ℝ×H => x.1 • x.2) := contDiff_fst.smul contDiff_snd

theorem scalar_vector_map_growth (H:Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] (k:ℕ) :
    ∃C:ℝ,0≤C ∧ ∃a:ℕ,∀x:ℝ×H,
      ‖iteratedFDeriv ℝ k (fun y:ℝ×H => y.1 • y.2) x‖≤C*(1+‖x‖)^a := by
  exact iterated_polynomial_growth_bilinear (ContinuousLinearMap.lsmul ℝ ℝ)
    (fun x:ℝ×H => x.1) (fun x:ℝ×H => x.2) contDiff_fst contDiff_snd
    (linear_map_all_derivatives_growth (ContinuousLinearMap.fst ℝ ℝ H))
    (linear_map_all_derivatives_growth (ContinuousLinearMap.snd ℝ ℝ H)) k
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_vector_map_growth
