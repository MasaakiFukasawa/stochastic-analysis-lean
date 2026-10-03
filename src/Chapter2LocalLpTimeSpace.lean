import Chapter2LocalLpPowerConvergence
import Chapter2ArbitraryTimeMetric

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The exact nonmonotone time horizons allowed in the manuscript. -/
noncomputable def localLpTimeSet {T : EReal} [Fact (0 ≤ T)]
    (t : ClosedTime T) : Set (Iio (⊤ : ClosedTime T)) := {s | s.val ≤ t}

theorem local_lp_time_set_measurable {T : EReal} [Fact (0 ≤ T)] (t : ClosedTime T) :
    MeasurableSet (localLpTimeSet t) := measurable_subtype_coe measurableSet_Iic

theorem local_lp_time_cover {T : EReal} [Fact (0 ≤ T)]
    (u : ℕ → ClosedTime T) (hu : ⨆ n, u n = ⊤) : ⋃ n, localLpTimeSet (u n) = univ := by
  apply eq_univ_of_forall
  intro s
  have hh : s.val < ⨆ n, u n := by rw [hu]; exact s.property
  obtain ⟨n,hn⟩ := lt_iSup_iff.mp hh
  exact mem_iUnion.mpr ⟨n,hn.le⟩

/-- Completeness of the displayed series distance after its zero-distance
quotient, without assuming the horizon sequence monotone or the measure finite. -/
theorem local_lp_time_quotient_complete {T : EReal} [Fact (0 ≤ T)]
    (μ : Measure (Iio (⊤ : ClosedTime T))) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : ℕ → ClosedTime T) :
    CompleteSpace (SeparationQuotient (LocalLpFunctions μ p (fun n => localLpTimeSet (u n)))) :=
  local_lp_quotient_complete μ p _ (fun n => local_lp_time_set_measurable (u n))

/-- Series-distance convergence equals the printed pth-power integral
convergence on every finite prefix. The horizons need not be monotone. -/
theorem local_lp_time_convergence {T : EReal} [Fact (0 ≤ T)]
    (μ : Measure (Iio (⊤ : ClosedTime T))) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (u : ℕ → ClosedTime T) (hut : ∀ n, u n < ⊤)
    (huc : ⨆ n, u n = ⊤)
    (f : ℕ → Iio (⊤ : ClosedTime T) → ℝ) (g : Iio (⊤ : ClosedTime T) → ℝ)
    (hf : ∀ n j, MemLp (f n) p (μ.restrict (localLpTimeSet (u j))))
    (hg : ∀ j, MemLp g p (μ.restrict (localLpTimeSet (u j)))) :
    Tendsto (fun n => localLpDistance μ p (fun j => localLpTimeSet (u j))
      (f n) g (hf n) hg) atTop (𝓝 0) ↔
    ∀ t : Iio (⊤ : ClosedTime T),
      Tendsto (fun n => ∫ s in localLpTimeSet t.val, |f n s-g s| ^ p.toReal ∂μ) atTop (𝓝 0) := by
  have hBK (t : Iio (⊤ : ClosedTime T)) : ∃ j, localLpTimeSet t.val ⊆ localLpTimeSet (u j) := by
    have hh : t.val < ⨆ n, u n := by rw [huc]; exact t.property
    obtain ⟨j,hj⟩ := lt_iSup_iff.mp hh
    exact ⟨j,fun s hs => hs.trans hj.le⟩
  rw [local_lp_cofinal_convergence μ p (fun j => localLpTimeSet (u j))
    (fun t : Iio (⊤ : ClosedTime T) => localLpTimeSet t.val)
    (fun j => ⟨⟨u j,hut j⟩,Subset.rfl⟩) hBK f g hf hg]
  apply forall_congr'
  intro t
  obtain ⟨j,hj⟩ := hBK t
  have hi n := ((hf n j).sub (hg j)).mono_measure (Measure.restrict_mono hj le_rfl)
  exact finite_lp_convergence_power_iff (μ.restrict (localLpTimeSet t.val)) p hp (fun n => f n-g) hi

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_lp_time_quotient_complete
#print axioms Asakura.Chapter2Complete.local_lp_time_convergence
