import Chapter12PolygonalCellData
import Mathlib.Topology.ContinuousMap.Compact

open Set Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

noncomputable def polygonalCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (T h : ℝ) (n : ℕ) : C(Icc (0:ℝ) T,E) :=
  ⟨fun t => polygonalPath f h n t,(polygonalPath_continuous f h n).comp continuous_subtype_val⟩

theorem constructed_polygonal_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (T h : ℝ) (hh : 0<h) (n : ℕ) (hn : 0<n)
    (hT : (n:ℝ)*h=T) (g : C(Icc (0:ℝ) T,E)) (hg : ∀ t,g t=f t) :
    ‖polygonalCompact f T h n‖≤‖g‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  obtain ⟨l,r,a,ha,ha1,_,_,_,he⟩ := polygonal_cell_data f T h hh n hn hT t
  change ‖polygonalPath f h n t‖≤‖g‖
  rw [he,← hg l,← hg r]
  simpa only [sub_zero] using convex_interpolation_error (g l) (g r) 0 a ‖g‖ ha ha1
    (by simpa using g.norm_coe_le_norm l) (by simpa using g.norm_coe_le_norm r)

theorem constructed_polygonal_convergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (T : ℝ) (g : C(Icc (0:ℝ) T,E)) (hg : ∀ t,g t=f t)
    (h : ℕ → ℝ) (N : ℕ → ℕ) (hh : ∀ n,0<h n) (hN : ∀ n,0<N n)
    (hT : ∀ n,(N n:ℝ)*h n=T) (hl : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => polygonalCompact f T (h n) (N n)) atTop (𝓝 g) := by
  have hu := CompactSpace.uniformContinuous_of_continuous g.continuous
  apply Metric.tendsto_atTop.mpr
  intro e he
  obtain ⟨d,hd,hdu⟩ := Metric.uniformContinuous_iff.mp hu (e/2) (by linarith)
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp (hl.eventually (gt_mem_nhds hd))
  refine ⟨n0,fun n hn => ?_⟩
  rw [dist_eq_norm]
  have heh : 0≤e/2 := by linarith
  have hb : ‖polygonalCompact f T (h n) (N n)-g‖≤e/2 := by
    apply (ContinuousMap.norm_le _ heh).mpr
    intro t
    obtain ⟨l,r,a,ha,ha1,hlt,htr,hw,heq⟩ := polygonal_cell_data f T (h n) (hh n) (N n) (hN n) (hT n) t
    have hld : dist l t<d := by
      rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hlt)]
      linarith [hn0 n hn]
    have hrd : dist r t<d := by
      rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr htr)]
      linarith [hn0 n hn]
    change ‖polygonalPath f (h n) (N n) t-g t‖≤e/2
    rw [heq,← hg l,← hg r]
    exact convex_interpolation_error _ _ _ _ _ ha ha1
      (by simpa only [dist_eq_norm] using (hdu hld).le)
      (by simpa only [dist_eq_norm] using (hdu hrd).le)
  exact hb.trans_lt (by linarith)

end Asakura.Chapter12
