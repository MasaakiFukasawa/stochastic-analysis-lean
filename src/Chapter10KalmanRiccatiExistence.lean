import Chapter10KalmanLocalRiccati
import Chapter10RiccatiNoEscape
import Chapter10RiccatiContinuation

open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The Kalman Riccati equation has a positive-semidefinite solution on every
finite horizon. Existence, covariance positivity and nonescape are connected. -/
theorem kalman_riccati_finite_exists {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d q r : ℕ} (B : BrownianSystem P (q+r))
    (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (G : ℝ → Matrix (Fin d) (Fin q) ℝ)
    (C : ℝ → Matrix (Fin r) (Fin d) ℝ) (D J : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (hA : Continuous A) (hG : Continuous G) (hC : Continuous C) (hD : Continuous D) (hJ : Continuous J)
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) (hJD : ∀ t∈Ico 0 T,J t*D t=1) (hDJ : ∀ t∈Ico 0 T,D t*J t=1) :
    ∃ S : ℝ → Matrix (Fin d) (Fin d) ℝ,Continuous S ∧
      S 0=(fun i j => ∫ w,ξ w i*ξ w j ∂P) ∧
      (∀ t∈Ico 0 T,HasDerivWithinAt S
        (A t*S t+S t*(A t).transpose+G t*(G t).transpose-S t*((C t).transpose*((J t).transpose*J t)*C t)*S t) (Ici t) t) ∧
      ∀ t∈Icc 0 T,(S t).PosSemidef := by
  letI : MeasurableSpace Ω := m
  let S₀ : Matrix (Fin d) (Fin d) ℝ := fun i j => ∫ w,ξ w i*ξ w j ∂P
  let Q := fun t => G t*(G t).transpose
  let H := fun t => (C t).transpose*((J t).transpose*J t)*C t
  have hQc : Continuous Q := by dsimp [Q]; fun_prop
  have hHc : Continuous H := by dsimp [H]; fun_prop
  have hi i : MemLp (fun w => ξ w i) 2 P := by
    apply hξ2.norm.of_le ((measurable_pi_apply i).comp (hξ.mono (B.le _) le_rfl)).aestronglyMeasurable
    exact ae_of_all _ fun w => by simpa only [norm_norm,Function.comp_apply] using norm_le_pi_norm (ξ w) i
  have hS₀ : ‖S₀‖≤S₀.trace := covariance_norm_le_trace P (fun i w => ξ w i) hi
  have hS₀p : 0≤S₀.trace := (norm_nonneg _).trans hS₀
  obtain ⟨a,ha⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hA.continuousOn
  have hQt : Continuous (fun t => (Q t).trace) :=
    continuous_finsetSum _ (fun i _ => (continuous_apply i).comp ((continuous_apply i).comp hQc))
  obtain ⟨v,hv⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hQt.continuousOn
  let α := max a 0
  let β := max v 0
  let c := 2*(d:ℝ)^2*α
  have hα : 0≤α := le_max_right _ _
  have hβ : 0≤β := le_max_right _ _
  have hc : 0≤c := by dsimp [c]; positivity
  let L := gronwallBound S₀.trace c β T
  have hL : S₀.trace≤L := by
    have hh := gronwallBound_mono hS₀p hβ hc hT
    simpa only [gronwallBound_x0] using hh
  have hap : ∀ τ∈Icc 0 T,∀ S : ℝ → Matrix (Fin d) (Fin d) ℝ,
      Continuous S → S 0=S₀ →
      (∀ t∈Ico 0 τ,HasDerivWithinAt S (A t*S t+S t*(A t).transpose+Q t-S t*H t*S t) (Ici t) t) → ‖S τ‖≤L := by
    intro τ hτ S hSc hSzero hSd
    have hJD' t (ht : t∈Ico 0 τ) := hJD t ⟨ht.1,ht.2.trans_le hτ.2⟩
    have hDJ' t (ht : t∈Ico 0 τ) := hDJ t ⟨ht.1,ht.2.trans_le hτ.2⟩
    have hloc := kalman_local_riccati_bounds P B A G C D J hA hG hC hD hJ ξ hξ hξ2 τ hτ.1
      hJD' hDJ' S hSc hSzero hSd
    let K := fun t => S t*(C t).transpose*((J t).transpose*J t)
    have hg t (ht : t∈Ico 0 τ) := kalman_gain_times_noise_covariance (S t) (C t) (D t) (J t) (hJD' t ht) (hDJ' t ht)
    have hSsym t (ht : t∈Ico 0 τ) : (S t).transpose=S t := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using (hloc t ⟨ht.1,ht.2.le⟩).1.isHermitian.eq
    have hR t (_ : t∈Ico 0 τ) : (D t*(D t).transpose).PosSemidef := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose (D t)
    have hder t (ht : t∈Ico 0 τ) : HasDerivWithinAt S
        (A t*S t+S t*(A t).transpose+Q t-K t*C t*S t) (Ici t) t := by
      dsimp only [K]
      rw [kalman_gain_riccati_term]
      exact hSd t ht
    have hbd := riccati_no_escape S A Q K C (fun t => D t*(D t).transpose) τ α β hτ.1 hα hβ
      hSc.continuousOn hder hSsym hR hg (fun t ht => (hloc t ht).2)
      (fun t ht => (ha t ⟨ht.1,ht.2.le.trans hτ.2⟩).trans (le_max_left _ _))
      (fun t ht => (le_abs_self (Q t).trace).trans
        ((hv t ⟨ht.1,ht.2.le.trans hτ.2⟩).trans (le_max_left _ _))) τ ⟨hτ.1,le_rfl⟩
    rw [hSzero] at hbd
    exact hbd.trans (gronwallBound_mono hS₀p hβ hc hτ.2)
  obtain ⟨S,hSc,hSzero,hSd,_⟩ := riccati_exists_from_apriori A H Q hA hHc hQc S₀ T L hT
    (hS₀p.trans hL) (hS₀.trans hL) hap
  have hloc := kalman_local_riccati_bounds P B A G C D J hA hG hC hD hJ ξ hξ hξ2 T hT hJD hDJ S hSc hSzero hSd
  exact ⟨S,hSc,hSzero,hSd,fun t ht => (hloc t ht).1⟩

end Asakura.Chapter10
