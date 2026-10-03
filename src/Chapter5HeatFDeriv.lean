import Chapter5HeatEndpoint
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter5

/-- Vector-valued bounded-derivative Gaussian averaging, also applicable
to the derivative itself when checking preservation of C² regularity. -/
theorem averaged_bounded_fderiv {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    (ν : Measure E) [IsProbabilityMeasure ν] (hi : Integrable (fun z : E => z) ν)
    (f : E → V) (D : E → E →L[ℝ] V)
    (hd : ∀ x, HasFDerivAt f (D x) x) (hDc : Continuous D)
    (C : ℝ≥0) (hDb : ∀ x, ‖D x‖ ≤ C) :
    (∀ x t, HasFDerivAt (fun y => ∫ z, f (y+Real.sqrt t • z) ∂ν)
      (∫ z, D (x+Real.sqrt t • z) ∂ν) x) ∧
    Continuous (fun p : E × ℝ => ∫ z, D (p.1+Real.sqrt p.2 • z) ∂ν) ∧
    (∀ x t, ‖∫ z, D (x+Real.sqrt t • z) ∂ν‖ ≤ C) ∧
    (∀ x, (∫ z, D (x+Real.sqrt 0 • z) ∂ν) = D x) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hl : LipschitzWith C f := lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hd x).differentiableAt) (fun x => by
      rw [(hd x).fderiv]
      exact_mod_cast hDb x)
  have hfi x t : Integrable (fun z => f (x+Real.sqrt t • z)) ν := by
    have hb : Integrable (fun z : E => ‖f x‖+(C:ℝ)*Real.sqrt t*‖z‖) ν :=
      (integrable_const _).add (hi.norm.const_mul _)
    apply hb.mono' (hfc.comp (by fun_prop)).aestronglyMeasurable
    apply ae_of_all
    intro z
    have hh := hl.dist_le_mul (x+Real.sqrt t • z) x
    simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg t)] at hh
    calc
      ‖f (x+Real.sqrt t • z)‖ ≤ ‖f x‖+‖f (x+Real.sqrt t • z)-f x‖ := by
        simpa only [add_sub_cancel] using norm_add_le (f x) (f (x+Real.sqrt t • z)-f x)
      _ ≤ ‖f x‖+(C:ℝ)*(Real.sqrt t*‖z‖) := add_le_add le_rfl hh
      _ = _ := by ring
  refine ⟨?_,?_,?_,?_⟩
  · intro x t
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := ν) (s := univ) (bound := fun _ => (C:ℝ))
      (F' := fun y z => D (y+Real.sqrt t • z)) univ_mem
    · exact Eventually.of_forall fun y => (hfc.comp (by fun_prop)).aestronglyMeasurable
    · exact hfi x t
    · exact (hDc.comp (by fun_prop)).aestronglyMeasurable
    · exact ae_of_all _ fun z y _ => hDb _
    · exact integrable_const _
    · exact ae_of_all _ fun z y _ => by
        simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using
          (hd (y+Real.sqrt t • z)).comp y ((hasFDerivAt_id y).add_const (Real.sqrt t • z))
  · apply continuous_iff_continuousAt.mpr
    intro p
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (C:ℝ))
    · exact Eventually.of_forall fun q => (hDc.comp (by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall fun q => ae_of_all _ fun z => hDb _
    · exact integrable_const _
    · exact ae_of_all _ fun z => (hDc.comp (by fun_prop)).continuousAt
  · intro x t
    have hdi : Integrable (fun z => D (x+Real.sqrt t • z)) ν :=
      Integrable.of_bound (hDc.comp (by fun_prop)).aestronglyMeasurable C (ae_of_all _ fun z => hDb _)
    calc
      _ ≤ ∫ z, ‖D (x+Real.sqrt t • z)‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : E, (C:ℝ) ∂ν := integral_mono hdi.norm (integrable_const _) (fun z => hDb _)
      _ = C := by simp
  · intro x; simp

end Asakura.Chapter5
