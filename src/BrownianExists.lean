import UnitBrownianZero
import GluedMoments
import CopiesMoments
import Mathlib.Probability.BrownianMotion.Basic

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
namespace Asakura

/-- Appendix C: existence of standard Brownian motion on the half-line,
with a common full event for every local Holder exponent 0 ≤ α < 1/2. -/
theorem brownian_motion_exists :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P ∧ ∃ X : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable (X t)) ∧ (∀ ω, Continuous (fun t => X t ω)) ∧
      IsBrownianReal X P ∧
      ∀ᵐ ω ∂P, ∀ α : ℝ, 0 ≤ α → α < 1/2 → ∀ N : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ≥0, s ≤ N → t ≤ N →
          dist (X s ω) (X t ω) ≤ C * (dist s t)^α := by
  classical
  obtain ⟨Ω₀,m₀,Q,hQ,Y,hYm,hYc,hY0,hYg,hm,hc,hH⟩ := unit_brownian_zero_exists
  letI := m₀
  letI := hQ
  obtain ⟨Ω,mΩ,P,ξ,hξm,hξ,hI,hP⟩ := exists_iid ℕ Q
  letI := mΩ
  letI := hP
  let W : (ℕ × UnitCube 1) → Ω → ℝ := fun p => Y p.2 ∘ ξ p.1
  have hWg : IsGaussianProcess W P := independent_copies_gaussian Y hYm hYg ξ hξ hI
  have hW0 : ∀ k ω, W (k,cubeZero) ω = 0 := fun k ω => hY0 _
  have hWm (p : ℕ × UnitCube 1) : Measurable (W p) := (hYm p.2).comp (hξm p.1)
  have hWl (p : ℕ × UnitCube 1) : MemLp (W p) 2 P := (hWg.hasGaussianLaw_eval p).memLp_two
  have hWmean (p : ℕ × UnitCube 1) : (∫ ω, W p ω ∂P) = 0 := copies_mean Y hYm hm ξ hξ _ _
  have hWcov (k l : ℕ) (s t : UnitCube 1) : cov[W (k,s),W (l,t);P] =
      if k = l then min (s.val 0) (t.val 0) else 0 := copies_covariance Y hYm hYg hm hc ξ hξ hI k l s t
  let X : ℝ≥0 → Ω → ℝ := fun t => gluedProcess W t
  have hXm (t : ℝ≥0) : Measurable (X t) := glued_process_measurable W hWm hW0 t
  have hXc (ω : Ω) : Continuous (fun t => X t ω) := by
    have hcont := gluedPath_continuous (fun k u => Y u (ξ k ω))
      (fun k => hY0 _) (fun k => hYc _)
    exact hcont.comp continuous_subtype_val
  have hXg : IsGaussianProcess X P := (glued_process_gaussian W hWg hW0).comp_right
    (fun t : ℝ≥0 => (t : ℝ))
  have hXmean (t : ℝ≥0) : (∫ ω, X t ω ∂P) = 0 := glued_process_mean W hWl hW0 hWmean t
  have hXcov (s t : ℝ≥0) : cov[X s,X t;P] = min (s : ℝ) (t : ℝ) :=
    glued_process_covariance W hWl hW0 hWcov s t s.coe_nonneg t.coe_nonneg
  have hB : IsBrownianReal X P :=
    ⟨hXg.isPreBrownianReal_of_covariance hXmean (fun s t hst =>
      (hXcov s t).trans (min_eq_left (by exact_mod_cast hst))), Eventually.of_forall hXc⟩
  refine ⟨Ω,mΩ,P,hP,X,hXm,hXc,hB,?_⟩
  have hcopies : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ α : ℝ, 0 ≤ α → α < 1/2 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s t,
        dist (Y s (ξ k ω)) (Y t (ξ k ω)) ≤ C * (dist s t)^α := by
    apply ae_all_iff.mpr
    intro k
    apply ae_of_ae_map (hξ k).aemeasurable (p := fun ω =>
      ∀ α : ℝ, 0 ≤ α → α < 1/2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : UnitCube 1,
        dist (Y s ω) (Y t ω) ≤ C * (dist s t)^α)
    rw [(hξ k).map_eq]
    exact hH
  filter_upwards [hcopies] with ω hω
  intro α hα hαh N
  choose C hC hbound using (fun k => hω k α hα hαh)
  refine ⟨∑ k ∈ Finset.range N, C k, Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  intro s t hs ht
  exact gluedPath_holder (fun k u => Y u (ξ k ω)) (fun k => hY0 _)
    α hα C hC hbound N s t (by exact_mod_cast hs) (by exact_mod_cast ht)
end Asakura
