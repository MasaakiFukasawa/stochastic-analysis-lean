import FullAuditIndependentSums
import Mathlib.Topology.Algebra.Order.Floor

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology NNReal
namespace Asakura.FullAudit

noncomputable def stepSum {Ω : Type*} (Z : ℕ → Ω → ℝ) (t : ℝ≥0) : Ω → ℝ :=
  partialSum Z ⌊(t : ℝ)⌋₊

theorem floor_right_eventually (t : ℝ≥0) :
    ∀ᶠ (s : ℝ≥0) in 𝓝[≥] t, ⌊(s : ℝ)⌋₊ = ⌊(t : ℝ)⌋₊ := by
  have hupper : ∀ᶠ s : ℝ≥0 in 𝓝 t, (s : ℝ) < (⌊(t : ℝ)⌋₊ : ℝ)+1 :=
    NNReal.continuous_coe.continuousAt.eventually (Iio_mem_nhds (Nat.lt_floor_add_one (t : ℝ)))
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds hupper] with s hs hu
  apply (Nat.floor_eq_iff s.property).mpr
  exact ⟨(Nat.floor_le t.property).trans (show (t : ℝ) ≤ (s : ℝ) from hs),hu⟩

theorem step_sum_right_continuous {Ω : Type*} (Z : ℕ → Ω → ℝ) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s => stepSum Z s ω) (Ici t) t := by
  apply (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ≥0 => stepSum Z t ω) (Ici t) t).congr_of_eventuallyEq
  · exact (floor_right_eventually t).mono fun s hs => by simp only [stepSum,hs]
  · rfl

/-- The smaller natural past suffices; no unjustified equality of sigma algebras is needed. -/
theorem step_sum_past_le_prefix {Ω : Type*} (Z : ℕ → Ω → ℝ) (t : ℝ≥0) :
    pastSigma (stepSum Z) t ≤ prefixSigma Z ⌊(t : ℝ)⌋₊ := by
  apply iSup_le
  intro s
  exact ((partial_sum_adapted Z ⌊(s.val : ℝ)⌋₊).mono
    (prefix_sigma_mono Z (Nat.floor_mono (show (s.val : ℝ) ≤ (t : ℝ) from s.property))) le_rfl).comap_le

/-- The full finite-time Lp martingale exercise, including right continuity and
 the null augmentation used in the manuscript's natural filtration. -/
theorem independent_step_sum_exercise {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hm : ∀ i, Measurable[m] (Z i)) (hi : iIndepFun Z P)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hmem : ∀ i, MemLp (Z i) p P)
    (hz : ∀ i, ∫ ω, Z i ω ∂P = 0) :
    (∀ t, Measurable[Asakura.nullAugmentation P (pastSigma (stepSum Z) t)] (stepSum Z t)) ∧
    (∀ t, MemLp (stepSum Z t) p P) ∧
    (∀ ω t, ContinuousWithinAt (fun s => stepSum Z s ω) (Ici t) t) ∧
    (∀ s t, s ≤ t → P[stepSum Z t | Asakura.nullAugmentation P (pastSigma (stepSum Z) s)] =ᵐ[P] stepSum Z s) := by
  have hsm : ∀ t, Measurable[m] (stepSum Z t) := fun t =>
    (partial_sum_adapted Z _).mono (prefix_sigma_le Z hm _) le_rfl
  have hsi : ∀ t, Integrable (stepSum Z t) P := fun t =>
    (partial_sum_memLp P Z p hmem _).integrable hp
  refine ⟨natural_augmented_adapted P (stepSum Z) hsm,
    (fun t => partial_sum_memLp P Z p hmem _),step_sum_right_continuous Z,?_⟩
  intro s t hst
  have hmain := independent_partial_sum_martingale P Z hm hi
    (fun i => (hmem i).integrable hp) hz ⌊(s : ℝ)⌋₊ ⌊(t : ℝ)⌋₊ (Nat.floor_mono hst)
  have hCE := condExp_congr_ae (m := pastSigma (stepSum Z) s) hmain
  have htower := condExp_condExp_of_le (step_sum_past_le_prefix Z s)
    (prefix_sigma_le Z hm _) (μ := P) (f := stepSum Z t)
  have hself : P[stepSum Z s | pastSigma (stepSum Z) s] = stepSum Z s :=
    condExp_of_stronglyMeasurable (past_sigma_le (stepSum Z) hsm s)
      (natural_process_adapted (stepSum Z) s).stronglyMeasurable (hsi s)
  have hraw : P[stepSum Z t | pastSigma (stepSum Z) s] =ᵐ[P] stepSum Z s := by
    exact htower.symm.trans (hCE.trans (EventuallyEq.of_eq hself))
  exact (conditional_null_augmentation P _ (past_sigma_le (stepSum Z) hsm s) _ (hsi t)).symm.trans hraw
end Asakura.FullAudit
