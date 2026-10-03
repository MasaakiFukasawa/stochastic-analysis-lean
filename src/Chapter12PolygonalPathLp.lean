import Chapter12PolygonalMesh
import Chapter12DominatedLpLimit
import Mathlib.Topology.ContinuousMap.Compact

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Uniform path convergence and the convex-combination bound imply Lp
convergence in the supremum norm. Measurability of the interpolant is the
only extra input; the domination is derived, not assumed. -/
theorem polygonal_path_Lp {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ)
    (B : Ω → C(Icc (0:ℝ) T,E))
    (Q : ℕ → Ω → C(Icc (0:ℝ) T,E))
    (l r : ℕ → Icc (0:ℝ) T → Icc (0:ℝ) T)
    (a : ℕ → Icc (0:ℝ) T → ℝ) (ha : ∀ n t,0≤a n t ∧ a n t≤1)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hb : ∀ n t,((l n t):ℝ)≤t ∧ (t:ℝ)≤r n t ∧ ((r n t):ℝ)-l n t≤h n)
    (hQ : ∀ n w t,Q n w t=(1-a n t) • B w (l n t)+a n t • B w (r n t))
    (hm : ∀ n,AEStronglyMeasurable (Q n) P)
    (p : ℝ≥0∞) (hp : 1≤p) (hpt : p≠⊤) (hB : MemLp B p P) :
    Tendsto (fun n => eLpNorm (Q n-B) p P) atTop (𝓝 0) := by
  apply dominated_Lp_limit P p hp hpt Q B B hB hm hB
  · intro n
    filter_upwards [] with w
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro t
    rw [hQ]
    simpa only [sub_zero] using convex_interpolation_error
      (B w (l n t)) (B w (r n t)) 0 (a n t) ‖B w‖ (ha n t).1 (ha n t).2
      (by simpa using (B w).norm_coe_le_norm (l n t))
      (by simpa using (B w).norm_coe_le_norm (r n t))
  · filter_upwards [] with w
    have hu := polygonal_mesh_uniform T (B w) (B w).continuous l r a ha h hh hb
    apply Metric.tendsto_atTop.mpr
    intro e he
    have heh : 0<e/2 := by linarith
    obtain ⟨N,hN⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hu (e/2) heh)
    refine ⟨N,fun n hn => ?_⟩
    rw [dist_eq_norm]
    have hn' : ‖Q n w-B w‖≤e/2 := by
      apply (ContinuousMap.norm_le _ heh.le).mpr
      intro t
      change ‖Q n w t-B w t‖≤e/2
      rw [hQ,← dist_eq_norm,dist_comm]
      exact (hN n hn t).le
    exact hn'.trans_lt (by linarith)

end Asakura.Chapter12
