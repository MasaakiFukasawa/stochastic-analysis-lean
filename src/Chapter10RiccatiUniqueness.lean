import Chapter10RiccatiLipschitz
import Mathlib.Analysis.Calculus.Deriv.Prod

open Set Matrix
open scoped Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Local uniqueness for the Riccati equation follows from its polynomial
Lipschitz bound on the compact ranges of the two candidate solutions. -/
theorem riccati_unique {d : ℕ} (A H Q S U : ℝ → Matrix (Fin d) (Fin d) ℝ) (T : ℝ)
    (hAc : ContinuousOn A (Icc 0 T)) (hHc : ContinuousOn H (Icc 0 T))
    (hSc : ContinuousOn S (Icc 0 T)) (hUc : ContinuousOn U (Icc 0 T))
    (hSd : ∀ t∈Ico 0 T,HasDerivWithinAt S (A t*S t+S t*(A t).transpose+Q t-S t*H t*S t) (Ici t) t)
    (hUd : ∀ t∈Ico 0 T,HasDerivWithinAt U (A t*U t+U t*(A t).transpose+Q t-U t*H t*U t) (Ici t) t)
    (h0 : S 0=U 0) : ∀ t∈Icc 0 T,S t=U t := by
  obtain ⟨a,ha⟩ := isCompact_Icc.exists_bound_of_continuousOn hAc
  obtain ⟨h,hh⟩ := isCompact_Icc.exists_bound_of_continuousOn hHc
  obtain ⟨s,hs⟩ := isCompact_Icc.exists_bound_of_continuousOn hSc
  obtain ⟨u,hu⟩ := isCompact_Icc.exists_bound_of_continuousOn hUc
  let R := max 0 (max s u)
  have hR : 0≤R := le_max_left _ _
  have hSb t (ht : t∈Icc 0 T) : ‖S t‖≤R := (hs t ht).trans ((le_max_left s u).trans (le_max_right _ _))
  have hUb t (ht : t∈Icc 0 T) : ‖U t‖≤R := (hu t ht).trans ((le_max_right s u).trans (le_max_right _ _))
  have he := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun t => S t-U t)
    (f' := fun t => (A t*S t+S t*(A t).transpose+Q t-S t*H t*S t)-
      (A t*U t+U t*(A t).transpose+Q t-U t*H t*U t))
    (K := 2*(d:ℝ)*max a 0+2*(d:ℝ)^2*max h 0*R) (a := 0) (b := T)
    (hSc.sub hUc) (fun t ht => (hSd t ht).sub (hUd t ht)) (sub_eq_zero.mpr h0) (by
      intro t ht
      apply (riccati_bounded_lipschitz (A t) (H t) (Q t) (S t) (U t) R hR
        (hSb t ⟨ht.1,ht.2.le⟩) (hUb t ⟨ht.1,ht.2.le⟩)).trans
      gcongr
      · exact (ha t ⟨ht.1,ht.2.le⟩).trans (le_max_left _ _)
      · exact (hh t ⟨ht.1,ht.2.le⟩).trans (le_max_left _ _))
  exact fun t ht => sub_eq_zero.mp (he t ht)

/-- Symmetry is preserved by the Riccati ODE; it is not an extra assumption
on the locally constructed solution. -/
theorem riccati_preserves_symmetry {d : ℕ} (A H Q S : ℝ → Matrix (Fin d) (Fin d) ℝ) (T : ℝ)
    (hAc : ContinuousOn A (Icc 0 T)) (hHc : ContinuousOn H (Icc 0 T))
    (hSc : ContinuousOn S (Icc 0 T))
    (hSd : ∀ t∈Ico 0 T,HasDerivWithinAt S (A t*S t+S t*(A t).transpose+Q t-S t*H t*S t) (Ici t) t)
    (hH : ∀ t∈Ico 0 T,(H t).transpose=H t) (hQ : ∀ t∈Ico 0 T,(Q t).transpose=Q t)
    (h0 : (S 0).transpose=S 0) : ∀ t∈Icc 0 T,(S t).transpose=S t := by
  have htc : ContinuousOn (fun t => (S t).transpose) (Icc 0 T) :=
    continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun j =>
      (continuous_apply i).comp_continuousOn ((continuous_apply j).comp_continuousOn hSc)))
  have htd t (ht : t∈Ico 0 T) : HasDerivWithinAt (fun t => (S t).transpose)
      (A t*(S t).transpose+(S t).transpose*(A t).transpose+Q t-(S t).transpose*H t*(S t).transpose) (Ici t) t := by
    have hd : HasDerivWithinAt (fun t => (S t).transpose)
        (A t*S t+S t*(A t).transpose+Q t-S t*H t*S t).transpose (Ici t) t :=
      hasDerivWithinAt_pi.mpr (fun i => hasDerivWithinAt_pi.mpr (fun j =>
        hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp (hSd t ht) j) i))
    have he : (A t*S t+S t*(A t).transpose+Q t-S t*H t*S t).transpose=
        A t*(S t).transpose+(S t).transpose*(A t).transpose+Q t-(S t).transpose*H t*(S t).transpose := by
      simp only [transpose_sub,transpose_add,transpose_mul,transpose_transpose,hH t ht,hQ t ht]
      noncomm_ring
    rw [he] at hd
    exact hd
  exact riccati_unique A H Q (fun t => (S t).transpose) S T hAc hHc htc hSc htd hSd h0

end Asakura.Chapter10
