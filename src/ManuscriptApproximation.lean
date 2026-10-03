import ManuscriptRepresentative

/-! Exact dyadic truncation from app0.tex (phin), for nonnegative real-valued f.
This closes the approximation input of the manuscript's representative proof. -/
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Asakura

noncomputable def manuscriptPhi (n : ℕ) (x : ℝ) : ℝ :=
  min (n : ℝ) (roundDown n x)

theorem manuscript_roundDown_monotone (n : ℕ) : Monotone (roundDown n) := by
  intro x y hxy
  unfold roundDown
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Int.floor_mono (mul_le_mul_of_nonneg_left hxy (by positivity : (0:ℝ) ≤ 2^n))

theorem manuscript_roundDown_nat (n : ℕ) : roundDown n (n : ℝ) = n := by
  have heq : (2 : ℝ)^n * n = ((2^n * (n : ℤ) : ℤ) : ℝ) := by push_cast; ring
  unfold roundDown
  rw [heq, Int.floor_intCast]
  push_cast
  field_simp

theorem manuscript_phi_clipped (n : ℕ) (x : ℝ) :
    manuscriptPhi n x = roundDown n (min (n : ℝ) x) := by
  by_cases h : x ≤ (n : ℝ)
  · rw [min_eq_right h]
    exact min_eq_right ((roundDown_le n x).trans h)
  · have hn : (n : ℝ) ≤ x := le_of_not_ge h
    have hr := manuscript_roundDown_monotone n hn
    rw [manuscript_roundDown_nat] at hr
    simp [manuscriptPhi, min_eq_left hn, min_eq_left hr, manuscript_roundDown_nat]

theorem manuscript_phi_monotone (n : ℕ) : Monotone (manuscriptPhi n) := by
  intro x y hxy
  exact min_le_min_left _ (manuscript_roundDown_monotone n hxy)

theorem manuscript_phi_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ manuscriptPhi n x := by
  apply le_min (by positivity)
  unfold roundDown
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg (by positivity : (0:ℝ) ≤ 2^n) hx)

theorem manuscript_phi_increasing (x : ℝ) : Monotone (fun n => manuscriptPhi n x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact min_le_min (by exact_mod_cast Nat.le_succ n) (roundDown_refinement n x).1

theorem manuscript_phi_tendsto (x : ℝ) :
    Tendsto (fun n => manuscriptPhi n x) atTop (𝓝 x) := by
  have herr : Tendsto (fun n : ℕ => 1 / (2 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using (tendsto_const_nhds (x := x)).sub herr)
    (tendsto_const_nhds (x := x))
  · have hn : ∀ᶠ n : ℕ in atTop, x ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop x)
    filter_upwards [hn] with n hn
    apply le_min
    · have hp : 0 ≤ ((2 : ℝ)^n)⁻¹ := by positivity
      linarith
    · have he := roundDown_error n x
      simp only [one_div] at he
      linarith
  · exact Eventually.of_forall (fun n => (min_le_right _ _).trans (roundDown_le n x))

theorem manuscript_phi_simple {Ω : Type*} [m : MeasurableSpace Ω]
    (f : Ω → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) (n : ℕ) :
    ∃ s : SimpleFunc Ω ℝ≥0∞, ∀ x, s x = ENNReal.ofReal (manuscriptPhi n (f x)) := by
  classical
  let F : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (manuscriptPhi n (f x))
  have hFm : Measurable F := ((manuscript_phi_monotone n).measurable.comp hf).ennreal_ofReal
  let K : Set ℤ := Set.Icc 0 (2^n * (n : ℤ))
  let v : ℤ → ℝ≥0∞ := fun k => ENNReal.ofReal ((k : ℝ) / (2 : ℝ)^n)
  have hfinite : (Set.range F).Finite := by
    apply ((Set.finite_Icc (0 : ℤ) (2^n * (n : ℤ))).image v).subset
    rintro y ⟨x, rfl⟩
    refine ⟨⌊(2 : ℝ)^n * min (n : ℝ) (f x)⌋, ⟨?_, ?_⟩, ?_⟩
    · exact Int.floor_nonneg.mpr (mul_nonneg (by positivity) (le_min (by positivity) (hpos x)))
    · have h := Int.floor_mono (mul_le_mul_of_nonneg_left (min_le_left (n : ℝ) (f x))
        (by positivity : (0:ℝ) ≤ 2^n))
      have heq : (2 : ℝ)^n * n = ((2^n * (n : ℤ) : ℤ) : ℝ) := by push_cast; ring
      rw [heq, Int.floor_intCast] at h
      exact h
    · simp only [v, F, manuscript_phi_clipped, roundDown]
  exact ⟨⟨F, fun y => hFm (measurableSet_singleton y), hfinite⟩, fun _ => rfl⟩

theorem manuscript_nonnegative_real_version {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (G : MeasurableSpace Ω) (f : Ω → ℝ)
    (hf : @Measurable Ω ℝ (nullAugmentation (m := m) μ G) _ f)
    (hpos : ∀ x, 0 ≤ f x) :
    ∃ g : Ω → ℝ, @Measurable Ω ℝ G _ g ∧ f =ᵐ[μ] g := by
  choose s hs using fun n => manuscript_phi_simple
    (m := nullAugmentation (m := m) μ G) f hf hpos n
  apply manuscript_real_supremum_repair (m := m) μ G f hpos s
  intro x
  simp_rw [hs]
  apply iSup_eq_of_forall_le_of_tendsto (F := atTop)
  · intro n
    exact ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (roundDown_le n (f x)))
  · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (manuscript_phi_tendsto (f x))

theorem manuscript_real_version_by_simple_sup {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (G : MeasurableSpace Ω) (f : Ω → ℝ)
    (hf : @Measurable Ω ℝ (nullAugmentation (m := m) μ G) _ f) :
    ∃ g : Ω → ℝ, @Measurable Ω ℝ G _ g ∧ f =ᵐ[μ] g := by
  obtain ⟨gp, hgp, hep⟩ := manuscript_nonnegative_real_version (m := m) μ G
    (fun x => max (f x) 0) (hf.max measurable_const) (fun _ => le_max_right _ _)
  obtain ⟨gm, hgm, hem⟩ := manuscript_nonnegative_real_version (m := m) μ G
    (fun x => max (-f x) 0) (hf.neg.max measurable_const) (fun _ => le_max_right _ _)
  refine ⟨fun x => gp x - gm x, hgp.sub hgm, ?_⟩
  filter_upwards [hep, hem] with x hp hm
  rw [← hp, ← hm]
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -f x ≤ 0), sub_zero]
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -f x)]
    ring

end Asakura
