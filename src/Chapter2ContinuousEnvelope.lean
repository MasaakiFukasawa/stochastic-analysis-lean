import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Continuity

open Set Filter
open scoped Topology
namespace Asakura.Chapter2Complete

/-- A convergent sequence of continuous paths has a continuous absolute
supremum. This is the U_t = sup_j |X_j(t)| step of M_loc completeness.
Convergence is in the compact-open topology, i.e. locally uniform convergence
for real-valued paths on the manuscript's time interval. -/
theorem continuous_absolute_envelope
    {ι : Type*} [TopologicalSpace ι] [LocallyCompactSpace ι]
    (f : ℕ → C(ι,ℝ)) (g : C(ι,ℝ)) (hfg : Tendsto f atTop (𝓝 g)) :
    Continuous (fun t => ⨆ n, |f n t|) := by
  let K := insert g (range f)
  have hK : IsCompact K := hfg.isCompact_insert_range
  have hEval : Continuous (fun p : ι × C(ι,ℝ) => |p.2 p.1|) := by
    have h : Continuous (fun p : ι × C(ι,ℝ) => p.2 p.1) := continuous_snd.eval continuous_fst
    simpa only [Real.norm_eq_abs] using h.norm
  have hc : Continuous (fun t => sSup ((fun h : C(ι,ℝ) => |h t|) '' K)) :=
    hK.continuous_sSup hEval
  have he (t) : sSup ((fun h : C(ι,ℝ) => |h t|) '' K) = ⨆ n, |f n t| := by
    have hev : Continuous (fun h : C(ι,ℝ) => |h t|) := by
      have h : Continuous (fun h : C(ι,ℝ) => h t) := continuous_id.eval continuous_const
      simpa only [Real.norm_eq_abs] using h.norm
    have hb : BddAbove (range (fun n => |f n t|)) := by
      apply (hK.image hev).bddAbove.mono
      rintro y ⟨n,rfl⟩
      exact ⟨f n,mem_insert_of_mem _ (mem_range_self n),rfl⟩
    have hg : |g t| ≤ ⨆ n, |f n t| :=
      le_of_tendsto (hev.tendsto g |>.comp hfg)
        (Filter.Eventually.of_forall fun n => le_ciSup hb n)
    change sSup ((fun h : C(ι,ℝ) => |h t|) '' insert g (range f)) = _
    rw [image_insert_eq, ← range_comp]
    simp only [Function.comp_def]
    rw [csSup_insert hb (range_nonempty _)]
    exact max_eq_right hg
  simpa only [he] using hc

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_absolute_envelope
