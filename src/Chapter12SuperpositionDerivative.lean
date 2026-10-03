import Chapter12ContinuousMapOperator
import Chapter12MapTaylorBound

open scoped Topology NNReal
namespace Asakura.Chapter12
open Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem superposition_hasFDerivAt {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (D : E → E →L[ℝ] F) (hD : ∀ x,HasFDerivAt f (D x) x)
    (L : ℝ≥0) (hL : LipschitzWith L D) (u : C(K,E)) :
    HasFDerivAt (continuousMapSuperposition f (continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)))
      (continuousMapApply (continuousMapSuperposition D hL.continuous u)) u := by
  apply derivative_of_quadratic_remainder _ _ u L L.coe_nonneg
  intro h
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖f (u t+h t)-f (u t)-D (u t) (h t)‖≤(L:ℝ)*‖h‖^2
  have hh := map_quadratic_taylor_bound f D hD L hL (u t+h t) (u t)
  rw [add_sub_cancel_left] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (h.norm_coe_le_norm t) 2) L.coe_nonneg)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.superposition_hasFDerivAt
