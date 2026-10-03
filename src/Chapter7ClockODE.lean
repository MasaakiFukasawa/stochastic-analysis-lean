import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter7

/-- The clock ODE in the manuscript is strictly increasing; positivity
is derived from the nonzero diffusion coefficient. -/
theorem ode_clock_strictMono
    (A v : ℝ → ℝ) (hc : ContinuousOn A (Ici 0))
    (hv : ∀ s,0 < s → v s ≠ 0)
    (hd : ∀ s,0 < s → HasDerivAt A (1/(v s)^2) s) :
    StrictMonoOn A (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) hc
  intro s hs
  have hs' : 0 < s := by simpa only [interior_Ici,mem_Ioi] using hs
  rw [(hd s hs').deriv]
  exact one_div_pos.mpr (sq_pos_of_ne_zero (hv s hs'))

/-- The inverse-clock identity is differentiated only at positive times.
Continuity at zero suffices for the fundamental theorem of calculus, so
no two-sided differentiability assumption at the initial time is added. -/
theorem inverse_clock_ode_integral
    (A τ v : ℝ → ℝ)
    (hτc : ContinuousOn τ (Ici 0)) (hτ0 : τ 0 = 0)
    (hτp : ∀ t,0 < t → 0 < τ t)
    (hinv : ∀ t,0 ≤ t → A (τ t) = t)
    (hv : ∀ s,0 < s → v s ≠ 0)
    (hd : ∀ s,0 < s → HasDerivAt A (1/(v s)^2) s)
    (hint : ∀ t,0 ≤ t → IntervalIntegrable (fun u => (v (τ u))^2) volume 0 t) :
    (∀ t,0 < t → HasDerivAt τ ((v (τ t))^2) t) ∧
    (∀ t,0 ≤ t → τ t = ∫ u in 0..t,(v (τ u))^2) := by
  have hder t (ht : 0 < t) : HasDerivAt τ ((v (τ t))^2) t := by
    have hc : ContinuousAt τ t :=
      (hτc t ht.le).continuousAt (Ici_mem_nhds ht)
    have hi : ∀ᶠ y in 𝓝 t,A (τ y) = y := by
      filter_upwards [Ioi_mem_nhds ht] with y hy
      exact hinv y hy.le
    have hh := (hd (τ t) (hτp t ht)).of_local_left_inverse hc
      (ne_of_gt (one_div_pos.mpr (sq_pos_of_ne_zero (hv _ (hτp t ht))))) hi
    simpa only [one_div,inv_inv] using hh
  refine ⟨hder,?_⟩
  intro t ht
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (hτc.mono (fun _ hx => hx.1)) (fun u hu => hder u hu.1) (hint t ht)
  simpa only [hτ0,sub_zero] using h.symm

end Asakura.Chapter7
