import Chapter3ContinuousCommonOscillation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's essential-supremum bounds on a countable dense set
control the whole continuous path outside one null set. -/
theorem dense_essential_bound_common_path
    {Ω D ι : Type*} [MeasurableSpace Ω] [TopologicalSpace D] [Countable ι]
    (P : Measure Ω) (q : ι → D) (hq : DenseRange q)
    (X : D → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => X t ω))
    (δ : ℝ) (hδ : 0 ≤ δ) (hb : ∀ i, eLpNorm (X (q i)) ∞ P ≤ ENNReal.ofReal δ) :
    ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ δ := by
  have hi (i) : ∀ᵐ ω ∂P, ‖X (q i) ω‖ ≤ δ := by
    filter_upwards [ae_le_eLpNormEssSup (f := X (q i)) (μ := P)] with ω hω
    have he := hω.trans (eLpNormEssSup_le_eLpNorm_top.trans (hb i))
    simpa only [toReal_enorm,ENNReal.toReal_ofReal hδ] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  filter_upwards [ae_all_iff.mpr hi] with ω hω
  have he : (fun t => min ‖X t ω‖ δ) = (fun t => ‖X t ω‖) :=
    ((hc ω).norm.min continuous_const).ext_on hq (hc ω).norm
      (fun t ht => by obtain ⟨i,rfl⟩ := ht; exact min_eq_left (hω i))
  intro t
  rw [← congrFun he t]
  exact min_le_right _ _

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.dense_essential_bound_common_path
