/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import ManuscriptMeasure

/-! app0:459--487: c times a finite-valued simple minorant, increasing level
sets exhausting each fibre, continuity from below, then the supremum over c
and simple minorants. Adapted from the Mathlib proof, whose argument follows
the manuscript's argument. The target MCT theorem is not invoked. -/
open MeasureTheory Set Filter ENNReal NNReal
open MeasureTheory.SimpleFunc
open scoped Topology
namespace Asakura
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
local infixr:25 " →ₛ " => SimpleFunc

theorem manuscript_monotone_convergence {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f) :
    ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  set c : ℝ≥0 → ℝ≥0∞ := (↑)
  set F := fun a : α => ⨆ n, f n a
  refine le_antisymm ?_ (iSup_lintegral_le _)
  rw [lintegral_eq_nnreal]
  refine iSup_le fun s => iSup_le fun hsf => ?_
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  rcases ENNReal.lt_iff_exists_coe.1 ha with ⟨r, rfl, _⟩
  have ha : r < 1 := ENNReal.coe_lt_coe.1 ha
  let rs := s.map fun a => r * a
  have eq_rs : rs.map c = (const α r : α →ₛ ℝ≥0∞) * map c s := rfl
  have eq : ∀ p, rs.map c ⁻¹' {p} = ⋃ n, rs.map c ⁻¹' {p} ∩ { a | p ≤ f n a } := by
    intro p
    rw [← inter_iUnion]; nth_rw 1 [← inter_univ (map c rs ⁻¹' {p})]
    refine Set.ext fun x => and_congr_right fun hx => (iff_of_eq (true_iff _)).2 ?_
    by_cases p_eq : p = 0
    · simp [p_eq]
    simp only [coe_map, mem_preimage, Function.comp_apply, mem_singleton_iff] at hx
    subst hx
    have : r * s x ≠ 0 := by rwa [Ne, ← ENNReal.coe_eq_zero]
    have : s x ≠ 0 := right_ne_zero_of_mul this
    have : (rs.map c) x < ⨆ n : ℕ, f n x := by
      refine lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ?_) (hsf x)
      suffices r * s x < 1 * s x by simpa
      gcongr
    rcases lt_iSup_iff.1 this with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, le_of_lt hi⟩
  have mono : ∀ r : ℝ≥0∞, Monotone fun n => rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a } := by
    intro r i j h
    refine inter_subset_inter_right _ ?_
    simp_rw [subset_def, mem_ofPred]
    intro x hx
    exact le_trans hx (h_mono h x)
  have h_meas : ∀ n, MeasurableSet {a : α | map c rs a ≤ f n a} := fun n =>
    measurableSet_le (SimpleFunc.measurable _) (hf n)
  calc
    (r : ℝ≥0∞) * (s.map c).lintegral μ = ∑ r ∈ (rs.map c).range, r * μ (rs.map c ⁻¹' {r}) := by
      rw [← const_mul_lintegral, eq_rs, SimpleFunc.lintegral]
    _ = ∑ r ∈ (rs.map c).range, r * μ (⋃ n, rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      simp only [(eq _).symm]
    _ = ∑ r ∈ (rs.map c).range, ⨆ n, r * μ (rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) :=
      Finset.sum_congr rfl fun x _ => by rw [manuscript_measure_iUnion μ _ (fun n => (rs.map c).measurableSet_fiber x |>.inter (measurableSet_le measurable_const (hf n))) (mono x), ENNReal.mul_iSup]
    _ = ⨆ n, ∑ r ∈ (rs.map c).range, r * μ (rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      refine ENNReal.finsetSum_iSup_of_monotone fun p i j h ↦ ?_
      gcongr _ * μ ?_
      exact mono p h
    _ ≤ ⨆ n : ℕ, ((rs.map c).restrict { a | (rs.map c) a ≤ f n a }).lintegral μ := by
      gcongr with n
      rw [restrict_lintegral _ (h_meas n)]
      refine le_of_eq (Finset.sum_congr rfl fun r _ => ?_)
      congr 2 with a
      refine and_congr_right ?_
      simp +contextual
    _ ≤ ⨆ n, ∫⁻ a, f n a ∂μ := by
      simp only [← SimpleFunc.lintegral_eq_lintegral]
      gcongr with n a
      simp only [map_apply] at h_meas
      simp only [coe_map, restrict_apply _ (h_meas _), (· ∘ ·)]
      exact indicator_apply_le id


/-- app0:537: g_n = inf_{k>=n} f_k, then the preceding monotone theorem. -/
theorem manuscript_fatou (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) :
    ∫⁻ x, liminf (fun n => f n x) atTop ∂μ ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat]
  rw [manuscript_monotone_convergence (f := fun n x => ⨅ k ≥ n, f k x)
    (fun n => Measurable.biInf (Set.Ici n) (Set.to_countable _) (fun k _ => hf k))
    (by intro n m hnm x; exact iInf_le_iInf_of_subset (fun k hk => hnm.trans hk))]
  apply iSup_mono
  intro n
  apply le_iInf
  intro k
  apply le_iInf
  intro hk
  apply MeasureTheory.lintegral_mono
  intro x
  exact iInf₂_le k hk

/-- Countable simultaneous replacement by measurable versions, for ae use of Fatou. -/
theorem manuscript_fatou_ae (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, AEMeasurable (f n) μ) :
    ∫⁻ x, liminf (fun n => f n x) atTop ∂μ ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := by
  let F := fun n => (hf n).mk (f n)
  have heq : ∀ᵐ x ∂μ, ∀ n, f n x = F n x := ae_all_iff.mpr (fun n => (hf n).ae_eq_mk)
  have hint : ∀ n, (∫⁻ x, f n x ∂μ) = ∫⁻ x, F n x ∂μ :=
    fun n => lintegral_congr_ae (hf n).ae_eq_mk
  calc
    _ = ∫⁻ x, liminf (fun n => F n x) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [heq] with x hx
      simp_rw [hx]
    _ ≤ _ := manuscript_fatou F (fun n => (hf n).measurable_mk)
    _ = _ := by simp_rw [hint]

/-- app0:583: Fatou applied to the nonnegative difference bound - error.
This is the manuscript's argument (with bound = 2g), not decreasing-tail DCT. -/
theorem manuscript_dominated_zero (F : ℕ → α → ℝ≥0∞) (G : α → ℝ≥0∞)
    (hF : ∀ n, Measurable (F n)) (hG : Measurable G)
    (hbound : ∀ n, F n ≤ᵐ[μ] G) (hfinite : ∫⁻ x, G x ∂μ ≠ ∞)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, F n x ∂μ) atTop (𝓝 0) := by
  let H : ℕ → α → ℝ≥0∞ := fun n x => G x - F n x
  have hHm : ∀ n, Measurable (H n) := fun n => hG.sub (hF n)
  have hHt : ∀ᵐ x ∂μ, Tendsto (fun n => H n x) atTop (𝓝 (G x)) := by
    filter_upwards [hlim, ae_lt_top' hG.aemeasurable hfinite] with x hx htop
    simpa [H, Function.comp_def] using (ENNReal.continuous_sub_left htop.ne).continuousAt.tendsto.comp hx
  have hlo : (∫⁻ x, G x ∂μ) ≤ liminf (fun n => ∫⁻ x, H n x ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => H n x) atTop ∂μ :=
        lintegral_congr_ae (hHt.mono (fun x hx => hx.liminf_eq.symm))
      _ ≤ _ := manuscript_fatou H hHm
  have hHbound : ∀ n, (∫⁻ x, H n x ∂μ) ≤ ∫⁻ x, G x ∂μ :=
    fun n => lintegral_mono (fun x => tsub_le_self)
  have hHI : Tendsto (fun n => ∫⁻ x, H n x ∂μ) atTop (𝓝 (∫⁻ x, G x ∂μ)) :=
    tendsto_of_le_liminf_of_limsup_le hlo (limsup_le_of_le (h := Eventually.of_forall hHbound))
  have heq : ∀ n, (∫⁻ x, F n x ∂μ) = (∫⁻ x, G x ∂μ) - ∫⁻ x, H n x ∂μ := by
    intro n
    apply ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top hfinite (hHbound n))
    rw [← lintegral_add_left (hF n)]
    apply lintegral_congr_ae
    filter_upwards [hbound n] with x hx
    exact add_tsub_cancel_of_le hx
  simp_rw [heq]
  simpa [Function.comp_def] using (ENNReal.continuous_sub_left hfinite).continuousAt.tendsto.comp hHI

end Asakura
