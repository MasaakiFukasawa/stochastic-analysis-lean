import Chapter7BrownianCellIntegrand
import Chapter7VectorIntegralConstruction

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable def brownianGridIntegrand {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (h : ℝ) (n : ℕ) (z : Ω × ℝ) : ℝ :=
    ∑ k : Fin n,brownianCellIntegrand B u ((k:ℝ)*h) (((k:ℝ)+1)*h) z

lemma brownian_grid_integrand_regular {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (h : ℝ) (hh : 0≤h) (n : ℕ) :
    Measurable (brownianGridIntegrand B u h n) ∧
    (∀ b,0≤b → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => brownianGridIntegrand B u h n (z.1,z.2.val))) ∧
    (∀ b,0≤b → ∀ w,IntervalIntegrable (fun r => (brownianGridIntegrand B u h n (w,r))^2) volume 0 b) := by
  have hc (k : Fin n) := brownian_cell_integrand_regular P B u ((k:ℝ)*h) (((k:ℝ)+1)*h)
    (mul_nonneg (by positivity) hh)
  refine ⟨Finset.measurable_sum _ (fun k _ => (hc k).1),?_,?_⟩
  · intro b hb
    exact Finset.measurable_sum _ (fun k _ => (hc k).2.1 b hb)
  · intro b hb w
    let μ := volume.restrict (Ioc (0:ℝ) b)
    have hi (k : Fin n) : MemLp (fun r => brownianCellIntegrand B u ((k:ℝ)*h) (((k:ℝ)+1)*h) (w,r)) 2 μ := by
      have hm : Measurable (fun r => brownianCellIntegrand B u ((k:ℝ)*h) (((k:ℝ)+1)*h) (w,r)) :=
        (hc k).1.comp (measurable_const.prodMk measurable_id)
      apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp ((hc k).2.2 b hb w)
    have hs : MemLp (fun r => ∑ k : Fin n,brownianCellIntegrand B u ((k:ℝ)*h) (((k:ℝ)+1)*h) (w,r)) 2 μ :=
      memLp_finsetSum _ (fun k _ => hi k)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr
      ((memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mp hs)

end Asakura.Chapter7
