import Mathlib.Analysis.Calculus.Deriv.Prod
import Chapter10RiccatiTrace
import Chapter10CovarianceTraceBound

open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- An explicit finite-horizon bound for a Riccati solution after covariance
identification. This is the nonexplosion estimate used for continuation. -/
theorem riccati_no_escape {d r : ℕ}
    (S A Q : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (K : ℝ → Matrix (Fin d) (Fin r) ℝ) (C : ℝ → Matrix (Fin r) (Fin d) ℝ)
    (R : ℝ → Matrix (Fin r) (Fin r) ℝ) (T a q : ℝ) (hT : 0≤T) (ha0 : 0≤a) (hq0 : 0≤q)
    (hSc : ContinuousOn S (Icc 0 T))
    (hSd : ∀ t∈Ico 0 T,HasDerivWithinAt S
      (A t*S t+S t*(A t).transpose+Q t-K t*C t*S t) (Ici t) t)
    (hSsym : ∀ t∈Ico 0 T,(S t).transpose=S t)
    (hR : ∀ t∈Ico 0 T,(R t).PosSemidef)
    (hgain : ∀ t∈Ico 0 T,K t*R t=S t*(C t).transpose)
    (hbound : ∀ t∈Icc 0 T,‖S t‖≤(S t).trace)
    (ha : ∀ t∈Ico 0 T,‖A t‖≤a) (hq : ∀ t∈Ico 0 T,(Q t).trace≤q) :
    ∀ t∈Icc 0 T,‖S t‖≤gronwallBound (S 0).trace (2*(d:ℝ)^2*a) q T := by
  let f := fun t => (S t).trace
  let f' := fun t => (A t*S t+S t*(A t).transpose+Q t-K t*C t*S t).trace
  have hfc : ContinuousOn f (Icc 0 T) := by
    exact continuousOn_finset_sum _ (fun i _ => (continuous_apply i).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hSc))
  have hfd t (ht : t∈Ico 0 T) : HasDerivWithinAt f (f' t) (Ici t) t := by
    simpa only [f,f',Matrix.trace,Matrix.diag_apply] using
      HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
        hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp (hSd t ht) i) i)
  have hb t (ht : t∈Ico 0 T) : f' t≤(2*(d:ℝ)^2*a)*f t+q := by
    have hh := riccati_trace_bound (A t) (S t) (Q t) (K t) (C t) (R t)
      (hSsym t ht) (hR t ht) (hgain t ht) (hbound t ⟨ht.1,ht.2.le⟩)
    have hn : 0≤(S t).trace := (norm_nonneg _).trans (hbound t ⟨ht.1,ht.2.le⟩)
    apply hh.trans
    exact add_le_add (by gcongr; exact ha t ht) (hq t ht)
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hfc
    (fun t ht _ hlt => (hfd t ht).liminf_right_slope_le hlt) le_rfl hb
  have hnonneg : 0≤(S 0).trace := (norm_nonneg _).trans (hbound 0 ⟨le_rfl,hT⟩)
  intro t ht
  have hh := hgr t ht
  simp only [sub_zero] at hh
  exact (hbound t ht).trans (hh.trans (gronwallBound_mono hnonneg hq0 (by positivity) ht.2))

end Asakura.Chapter10
