import Chapter12ConstructedPolygonalConvergence
import Chapter12DominatedLpLimit
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem polygonalCompact_measurable {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → Ω → ℝ) (hf : ∀ t,Measurable (f t)) (T h : ℝ) (n : ℕ) :
    Measurable (fun w => polygonalCompact (fun t => f t w) T h n) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun w => f 0 w+∑ k∈Finset.range n,
    ((min (((k:ℝ)+1)*h) t-min ((k:ℝ)*h) t)/h) • (f (((k:ℝ)+1)*h) w-f ((k:ℝ)*h) w))
  fun_prop

theorem constructed_polygonal_Lp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℝ → Ω → ℝ) (hf : ∀ t,Measurable (f t)) (T : ℝ)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (he : ∀ w t,X w t=f t w)
    (h : ℕ → ℝ) (N : ℕ → ℕ) (hh : ∀ n,0<h n) (hN : ∀ n,0<N n)
    (hT : ∀ n,(N n:ℝ)*h n=T) (hl : Tendsto h atTop (𝓝 0))
    (p : ℝ≥0∞) (hp : 1≤p) (hpt : p≠⊤) (hX : MemLp X p P) :
    Tendsto (fun n => eLpNorm
      ((fun w => polygonalCompact (fun t => f t w) T (h n) (N n))-X) p P) atTop (𝓝 0) := by
  apply dominated_Lp_limit P p hp hpt _ X X hX
    (fun n => (polygonalCompact_measurable f hf T (h n) (N n)).aestronglyMeasurable) hX
  · intro n
    exact ae_of_all _ (fun w => constructed_polygonal_norm_bound (fun t => f t w) T
      (h n) (hh n) (N n) (hN n) (hT n) (X w) (he w))
  · exact ae_of_all _ (fun w => constructed_polygonal_convergence (fun t => f t w) T
      (X w) (he w) h N hh hN hT hl)

end Asakura.Chapter12
