import Chapter6BrownianBridgeTermBound
import Chapter6BrownianGridTermIntegrable
import Chapter6ConditionalFiniteSumBound
import Chapter6BridgeSumBound

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's estimate for the actual left-endpoint Brownian sums,
with the exact constant and a coefficient that can depend on grid time. -/
theorem brownian_bridge_grid_sum_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (hn : 0<n) (h : ℝ) (hh : 0<h)
    (b : ℕ → (Fin d → ℝ) → (Fin d → ℝ)) (hb : ∀ k,Measurable (b k)) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ k x,‖WithLp.toLp 2 (b k x)‖≤K) :
    let V := fun w i => B.W i (realTimeClamp ((n:ℝ)*h)) w
    let S := fun w => ∑ k∈range n,∑ i,b k (fun i => B.W i (realTimeClamp ((k:ℝ)*h)) w) i*
      (B.W i (realTimeClamp (((k:ℝ)+1)*h)) w-B.W i (realTimeClamp ((k:ℝ)*h)) w)
    Integrable S P ∧ ∀ᵐ w ∂P,|P[S|MeasurableSpace.comap V inferInstance] w|
      ≤K*(‖WithLp.toLp 2 (V w)‖+2*Real.sqrt ((d:ℝ)*((n:ℝ)*h))) := by
  let V := fun w i => B.W i (realTimeClamp ((n:ℝ)*h)) w
  let X := fun k w => ∑ i,b k (fun i => B.W i (realTimeClamp ((k:ℝ)*h)) w) i*
      (B.W i (realTimeClamp (((k:ℝ)+1)*h)) w-B.W i (realTimeClamp ((k:ℝ)*h)) w)
  let a := fun (k : ℕ) w => h/((n:ℝ)*h-(k:ℝ)*h)*K*
        (((n:ℝ)*h-(k:ℝ)*h)/((n:ℝ)*h)*‖WithLp.toLp 2 (V w)‖+Real.sqrt ((d:ℝ)*((n:ℝ)*h-(k:ℝ)*h)))
  have hi k (hk : k∈range n) : Integrable (X k) P :=
    brownian_grid_term_integrable P B h hh k (mem_range.mp hk) (b k) (hb k) K (hbound k)
  have hs := conditional_finite_sum_abs_bound P n X a hi (MeasurableSpace.comap V inferInstance)
    (fun k hk => brownian_bridge_grid_term_bound P B h hh k (mem_range.mp hk) (b k) (hb k) K hK (hbound k))
  refine ⟨integrable_finsetSum _ hi,?_⟩
  filter_upwards [hs] with w hw
  exact hw.trans (bridge_bound_sum n d hn h K ‖WithLp.toLp 2 (V w)‖ hh hK)

end Asakura.Chapter6
