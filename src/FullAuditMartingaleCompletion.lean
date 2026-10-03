import FullAuditMartingalePathDifference
import FullAuditConditionalLimit

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

/-- Completeness of the actual continuous-martingale representatives. The path
 variable is completed using the locally expanded Lp proof (rapid subsequence,
 summable uniform increments, MCT, continuous uniform limits, Fatou). Its
 terminal conditional identity is then obtained by the printed L2 contraction.
 The null-set augmentation is used explicitly to recover adapted representatives. -/
theorem continuous_martingale_cauchy_completion {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ℕ → ClosedTime T → Ω → ℝ)
    (hm : ∀ n t, Measurable[F t] (X n t)) (h2 : ∀ n t, MemLp (X n t) 2 P)
    (hc : ∀ n ω, Continuous (fun t => X n t ω))
    (hmart : ∀ n s t, s ≤ t → P[X n t | F s] =ᵐ[P] X n s)
    (hz : ∀ n, X n ⊥ =ᵐ[P] 0)
    (hC : CauchySeq (fun n => (h2 n ⊤).toLp (X n ⊤))) :
    ∃ Y : ClosedTime T → Ω → ℝ,
      (∀ t, Measurable[F t] (Y t)) ∧ (∀ t, MemLp (Y t) 2 P) ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ s t, s ≤ t → P[Y t | F s] =ᵐ[P] Y s) ∧ Y ⊥ =ᵐ[P] 0 ∧
      Tendsto (fun n => eLpNorm (X n ⊤-Y ⊤) 2 P) atTop (𝓝 0) := by
  let G := fun n => continuousPath (X n) (hc n)
  have hG (n : ℕ) : MemLp (G n) 2 P :=
    continuous_martingale_path_memLp P F hF hle (X n) (hm n) (h2 n) (hc n) (hmart n)
  let V := fun n => (hG n).toLp (G n)
  have hCV : CauchySeq V := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hC (ε/2) (half_pos hε)
    refine ⟨N,fun n hn k hk => ?_⟩
    have hbound := martingale_path_Lp_distance P F hF hle (X n) (X k)
      (hm n) (hm k) (h2 n) (h2 k) (hc n) (hc k) (hmart n) (hmart k)
    have ht := hN n hn k hk
    change dist (V n) (V k) < ε
    exact lt_of_le_of_lt hbound (by linarith)
  letI : CompleteSpace (Lp C(ClosedTime T,ℝ) 2 P) := current_lp_complete
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete hCV
  let Y := fun t ω => g ω t
  have hgm : StronglyMeasurable (g : Ω → C(ClosedTime T,ℝ)) := Lp.stronglyMeasurable g
  have hYm (t : ClosedTime T) : Measurable[m] (Y t) := (ContinuousMap.measurable_eval t).comp hgm.measurable
  have hY2 (t : ClosedTime T) : MemLp (Y t) 2 P :=
    (Lp.memLp g).of_le (hYm t).aestronglyMeasurable (Eventually.of_forall fun ω => (g ω).norm_coe_le_norm t)
  have hconv : Tendsto (fun n => eLpNorm (G n-(g : Ω → C(ClosedTime T,ℝ))) 2 P) atTop (𝓝 0) := by
    have ht := (current_lp_tendsto_Lp_iff_tendsto_eLpNorm_prime V g).mp hg
    apply ht.congr'
    exact Eventually.of_forall fun n => eLpNorm_congr_ae ((hG n).coeFn_toLp.sub EventuallyEq.rfl)
  have hpoint (t : ClosedTime T) : Tendsto (fun n => eLpNorm (X n t-Y t) 2 P) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    · exact fun n => zero_le
    · intro n
      apply eLpNorm_mono_ae (((hm n t).mono (hle t) le_rfl).sub (hYm t)).aestronglyMeasurable
      exact Eventually.of_forall fun ω => (G n ω-g ω).norm_coe_le_norm t
  have hclosed (t : ClosedTime T) : Y t =ᵐ[P] P[Y ⊤ | F t] :=
    conditional_l2_limit_identity P (hle t) (fun n => X n t) (fun n => X n ⊤) (Y t) (Y ⊤)
      (fun n => h2 n t) (fun n => h2 n ⊤) (hY2 t) (hY2 ⊤)
      (fun n => (hmart n t ⊤ le_top).symm) (hpoint t) (hpoint ⊤)
  have hYadapt (t : ClosedTime T) : Measurable[F t] (Y t) :=
    measurable_of_augmented_ae P (hle t) (hnull t) (Y t) (P[Y ⊤ | F t]) (hYm t)
      stronglyMeasurable_condExp.measurable (hclosed t)
  have hYmart (s t : ClosedTime T) (hst : s ≤ t) : P[Y t | F s] =ᵐ[P] Y s :=
    (condExp_congr_ae (hclosed t)).trans
      ((condExp_condExp_of_le (hF hst) (hle t)).trans (hclosed s).symm)
  have hYzero : Y ⊥ =ᵐ[P] 0 := by
    have he (n : ℕ) : eLpNorm (X n ⊥-Y ⊥) 2 P = eLpNorm (Y ⊥) 2 P := by
      rw [eLpNorm_congr_ae ((hz n).sub EventuallyEq.rfl)]
      simp only [zero_sub,eLpNorm_neg]
    have ht := hpoint ⊥
    simp only [he] at ht
    have hzNorm : eLpNorm (Y ⊥) 2 P = 0 := tendsto_nhds_unique tendsto_const_nhds ht
    exact (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hzNorm
  exact ⟨Y,hYadapt,hY2,fun ω => (g ω).continuous,hYmart,hYzero,hpoint ⊤⟩

end Asakura.FullAudit
