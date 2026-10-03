import Extended

/-! The finite-fibre replacement and countable-supremum steps of app0.tex:661--669.
The approximation sequence is an explicit input: this file does NOT silently
replace the manuscript's dyadic approximation by Mathlib's rational enumeration.
The original final supremum is ENNReal-valued; toReal supplies the null-set repair.
-/
open MeasureTheory Filter Set
open scoped ENNReal
namespace Asakura

theorem manuscript_simple_replacement {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (G : MeasurableSpace Ω)
    (s : @SimpleFunc Ω (nullAugmentation (m := m) μ G) ℝ≥0∞) :
    ∃ g : @SimpleFunc Ω G ℝ≥0∞, (fun x => s x) =ᵐ[μ] (fun x => g x) := by
  classical
  let R := @SimpleFunc.range Ω ℝ≥0∞ (nullAugmentation (m := m) μ G) s
  have hsets : ∀ a : R, ∃ B : Set Ω, MeasurableSet[G] B ∧
      s ⁻¹' {a.val} =ᵐ[μ] B := fun a => (@SimpleFunc.measurableSet_fiber Ω ℝ≥0∞ (nullAugmentation (m := m) μ G) s a.val).2
  choose B hB hBeq using hsets
  let pieces : R → @SimpleFunc Ω G ℝ≥0∞ := fun a =>
    @SimpleFunc.piecewise Ω ℝ≥0∞ G (B a) (hB a)
      (@SimpleFunc.const Ω ℝ≥0∞ G a.val) (@SimpleFunc.const Ω ℝ≥0∞ G 0)
  refine ⟨∑ a, pieces a, ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ a : R, (s x = a.val) = (x ∈ B a) := by
    apply ae_all_iff.mpr
    intro a
    filter_upwards [hBeq a] with x hx
    exact hx
  filter_upwards [hall] with x hx
  have hsum : (∑ a : R, pieces a) x =
      ∑ a : R, if s x = a.val then a.val else 0 := by
    have heval : ∀ F : Finset R, (∑ a ∈ F, pieces a) x = ∑ a ∈ F, pieces a x := by
      intro F
      induction F using Finset.induction_on with
      | empty => simp
      | @insert a F ha ih => simp [Finset.sum_insert, ha, SimpleFunc.coe_add, ih]
    rw [heval]
    simp only [pieces, SimpleFunc.piecewise_apply, SimpleFunc.const_apply, ← hx]
  rw [hsum]
  have hmem : s x ∈ R := (@SimpleFunc.mem_range Ω ℝ≥0∞ (nullAugmentation (m := m) μ G) s (s x)).mpr ⟨x, rfl⟩
  symm
  calc
    _ = (if s x = (⟨s x, hmem⟩ : R).val then (⟨s x, hmem⟩ : R).val else 0) := by
      apply Finset.sum_eq_single (⟨s x, hmem⟩ : R)
      · intro b hb hne
        have hne' : s x ≠ b.val := by
          intro heq
          exact hne (Subtype.ext heq.symm)
        simp [hne']
      · simp
    _ = s x := by simp

theorem manuscript_supremum_replacement {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (G : MeasurableSpace Ω) (f : Ω → ℝ≥0∞)
    (s : ℕ → @SimpleFunc Ω (nullAugmentation (m := m) μ G) ℝ≥0∞)
    (hsup : ∀ x, ⨆ n, s n x = f x) :
    ∃ g : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞ G _ g ∧ f =ᵐ[μ] g := by
  choose g hg using fun n => manuscript_simple_replacement (m := m) μ G (s n)
  refine ⟨fun x => ⨆ n, g n x, Measurable.iSup (fun n => (g n).measurable), ?_⟩
  have hall := ae_all_iff.mpr hg
  filter_upwards [hall] with x hx
  rw [← hsup x]
  exact iSup_congr hx

theorem manuscript_real_supremum_repair {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (G : MeasurableSpace Ω) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (s : ℕ → @SimpleFunc Ω (nullAugmentation (m := m) μ G) ℝ≥0∞)
    (hsup : ∀ x, ⨆ n, s n x = ENNReal.ofReal (f x)) :
    ∃ g : Ω → ℝ, @Measurable Ω ℝ G _ g ∧ f =ᵐ[μ] g := by
  obtain ⟨F, hFm, hF⟩ := manuscript_supremum_replacement (m := m) μ G
    (fun x => ENNReal.ofReal (f x)) s hsup
  refine ⟨fun x => (F x).toReal, hFm.ennreal_toReal, ?_⟩
  filter_upwards [hF] with x hx
  rw [← hx, ENNReal.toReal_ofReal (hf x)]

end Asakura
