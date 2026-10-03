import Chapter12ConstructedPolygonalLp
import Chapter12BrownianCompactPath
import Chapter12BrownianPathMoments
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Actual uniform-grid linear interpolation of Brownian paths converges
in every finite Lp supremum norm, p≥1. No convergence or moment hypothesis
on the interpolants is assumed. -/
theorem brownian_polygonal_Lp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0<T)
    (p : ℝ≥0∞) (hp : 1≤p) (hpt : p≠⊤) :
    Tendsto (fun n => eLpNorm
      ((fun w => polygonalCompact (fun t => B ⟨max t 0,le_max_right _ _⟩ w)
        T ((T:ℝ)/(n+1:ℕ)) (n+1))-brownianCompactPath B hc T) p P)
      atTop (𝓝 0) := by
  have hx : Measurable (brownianCompactPath B hc T) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact hm ⟨t.val,t.property.1⟩
  have hmem := brownian_path_memLp P B hB hm hc T (brownianCompactPath B hc T) hx
    (fun _ _ => rfl) p hpt
  apply constructed_polygonal_Lp P (fun t w => B ⟨max t 0,le_max_right _ _⟩ w)
    (fun t => hm _) T (brownianCompactPath B hc T) ?_
    (fun n => (T:ℝ)/(n+1:ℕ)) (fun n => n+1) ?_ (fun n => Nat.succ_pos n) ?_ ?_ p hp hpt hmem
  · intro w t
    change B ⟨t.val,t.property.1⟩ w=B ⟨max t.val 0,le_max_right _ _⟩ w
    simp only [max_eq_left t.property.1]
  · intro n
    exact div_pos (show 0<(T:ℝ) from hT) (by positivity)
  · intro n
    field_simp
  · exact (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (T:ℝ))

end Asakura.Chapter12
