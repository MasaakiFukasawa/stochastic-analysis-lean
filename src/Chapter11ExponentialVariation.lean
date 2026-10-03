import Chapter3ContinuousIntegralConstruction
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Exponentiation preserves the actual adapted local variation space.
The input need only have continuous finite-variation paths, not a continuous
time derivative. -/
theorem exponential_continuous_local_variation
    {Ω : Type*} {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (A : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hAc : ∀ w t,t<⊤ → ContinuousAt (fun s => A s w) t) :
    AdaptedLocalVariationWitness F (fun t w => Real.exp (A t w)) := by
  obtain ⟨τ,hs,hm,ht,hco,ha⟩ := hA.localizers
  refine ⟨τ,hs,hm,ht,hco,?_⟩
  intro n
  have hc w : Continuous (fun t => A (min (τ n w) t) w) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hAc w _ ((min_le_left _ _).trans_lt (ht n w))).comp
      (continuous_const.min continuous_id).continuousAt
  have hvc w : Continuous (fun t => Real.exp (A (min (τ n w) t) w)) := Real.continuous_exp.comp (hc w)
  have hv w : BoundedVariationOn (fun t => Real.exp (A (min (τ n w) t) w)) univ := by
    obtain ⟨R,hR⟩ := isCompact_univ.exists_bound_of_continuousOn (hc w).continuousOn
    have hLip : LipschitzOnWith (NNReal.mk (Real.exp R) (Real.exp_pos _).le) Real.exp (Iic R) := by
      apply (convex_Iic R).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (fun x hx => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      intro x hx
      change ‖Real.exp x‖≤Real.exp R
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr hx
    exact hLip.comp_boundedVariationOn
      (fun t _ => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hR t (mem_univ _)))
      ((ha n).boundedVariation w)
  obtain ⟨U,V,hUa,hVa,hUc,hVc,hUm,hVm,he⟩ := adapted_continuous_jordan_decomposition F hF
    (fun t w => Real.exp (A (min (τ n w) t) w)) (fun t => ((ha n).adapted t).exp) hvc hv
  exact ⟨U,V,fun t => ⟨hUa t,hVa t⟩,fun w => ⟨hUm w,hVm w⟩,
    fun w t => ⟨(hUc w).continuousAt.continuousWithinAt,(hVc w).continuousAt.continuousWithinAt⟩,he⟩

end Asakura.Chapter11
