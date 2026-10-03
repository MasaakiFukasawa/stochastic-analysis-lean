import ManuscriptApproximation
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura

/-- The original formula, with the necessary convention phi_n(infinity)=n. -/
noncomputable def manuscriptENNPhi (n : ℕ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ⊤ then n else ENNReal.ofReal (manuscriptPhi n x.toReal)

theorem manuscript_ennphi_le (n : ℕ) (x : ℝ≥0∞) : manuscriptENNPhi n x ≤ x := by
  by_cases hx : x = ⊤
  · simp [manuscriptENNPhi, hx]
  · simp only [manuscriptENNPhi, ite_eq_right hx]
    exact (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (roundDown_le n x.toReal))).trans_eq (ENNReal.ofReal_toReal hx)

theorem manuscript_ennphi_bound (n : ℕ) (x : ℝ≥0∞) : manuscriptENNPhi n x ≤ n := by
  by_cases hx : x = ⊤
  · simp [manuscriptENNPhi,hx]
  · have h := ENNReal.ofReal_le_ofReal (min_le_left (n : ℝ) (roundDown n x.toReal))
    simpa [manuscriptENNPhi,manuscriptPhi,hx] using h

theorem manuscript_ennphi_monotone (n : ℕ) : Monotone (manuscriptENNPhi n) := by
  intro x y hxy
  by_cases hy : y = ⊤
  · simpa [manuscriptENNPhi,hy] using manuscript_ennphi_bound n x
  have hx : x ≠ ⊤ := ne_top_of_le_ne_top hy hxy
  simp only [manuscriptENNPhi,ite_eq_right hx,ite_eq_right hy]
  exact ENNReal.ofReal_le_ofReal (manuscript_phi_monotone n (ENNReal.toReal_mono hy hxy))

theorem manuscript_ennphi_increasing (x : ℝ≥0∞) : Monotone (fun n => manuscriptENNPhi n x) := by
  intro n m hnm
  by_cases hx : x = ⊤
  · simpa [manuscriptENNPhi,hx] using (show (n : ℝ≥0∞) ≤ m by exact_mod_cast hnm)
  · simp only [manuscriptENNPhi,ite_eq_right hx]
    exact ENNReal.ofReal_le_ofReal (manuscript_phi_increasing x.toReal hnm)

theorem manuscript_ennphi_iSup (x : ℝ≥0∞) : (⨆ n, manuscriptENNPhi n x) = x := by
  by_cases hx : x = ⊤
  · simp only [manuscriptENNPhi,hx,ite_true]
    exact iSup_eq_of_forall_le_of_tendsto (fun _ => le_top) ENNReal.tendsto_nat_nhds_top
  · apply iSup_eq_of_forall_le_of_tendsto (F := atTop) (fun n => manuscript_ennphi_le n x)
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (manuscript_phi_tendsto x.toReal)
    simpa [Function.comp_def, manuscriptENNPhi,hx,ENNReal.ofReal_toReal hx] using h

theorem manuscript_ennphi_simple {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    ∃ s : SimpleFunc Ω ℝ≥0∞, ∀ x, s x = manuscriptENNPhi n (f x) := by
  classical
  obtain ⟨s,hs⟩ := manuscript_phi_simple (fun x => (f x).toReal) hf.ennreal_toReal
    (fun x => ENNReal.toReal_nonneg) n
  let T : Set Ω := f ⁻¹' {⊤}
  have hT : MeasurableSet T := hf (measurableSet_singleton ⊤)
  refine ⟨SimpleFunc.piecewise T hT (SimpleFunc.const Ω (n : ℝ≥0∞)) s, ?_⟩
  intro x
  simp only [SimpleFunc.piecewise_apply, SimpleFunc.const_apply, hs, T,
    Set.mem_preimage, Set.mem_singleton_iff, manuscriptENNPhi]

end Asakura
