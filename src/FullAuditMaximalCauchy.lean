import FullAuditKolmogorovMaximal

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- Continuity from below extends a uniform finite maximum bound to all future indices. -/
theorem finite_maximum_to_all_indices {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (S : ℕ → Ω → ℝ)
    (n : ℕ) (ε B : ℝ)
    (h : ∀ N, P.real {ω | ∃ k ≤ N, ε ≤ |S (n+k) ω-S n ω|} ≤ B) :
    P {ω | ∃ k, ε ≤ |S (n+k) ω-S n ω|} ≤ ENNReal.ofReal B := by
  let A : ℕ → Set Ω := fun N => {ω | ∃ k ≤ N, ε ≤ |S (n+k) ω-S n ω|}
  have hm : Monotone A := by
    intro N M hNM ω hω
    obtain ⟨k,hk,hω⟩ := hω
    exact ⟨k,hk.trans hNM,hω⟩
  have he : {ω | ∃ k, ε ≤ |S (n+k) ω-S n ω|} = ⋃ N, A N := by
    ext ω
    simp only [mem_setOf_eq,mem_iUnion,A]
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨k,k,le_rfl,hk⟩
    · rintro ⟨N,k,hk,hω⟩
      exact ⟨k,hω⟩
  rw [he,hm.measure_iUnion]
  apply iSup_le
  intro N
  have hh := ENNReal.ofReal_le_ofReal (h N)
  change ENNReal.ofReal (P (A N)).toReal ≤ ENNReal.ofReal B at hh
  rwa [ENNReal.ofReal_toReal (measure_ne_top P (A N))] at hh

/-- A maximal tail bound tending to zero yields almost-sure Cauchy convergence.
The event intersection is handled before taking the countable error thresholds. -/
theorem maximal_tail_ae_cauchy {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (S : ℕ → Ω → ℝ) (v : ℕ → ℝ)
    (hv : Tendsto v atTop (𝓝 0))
    (hmax : ∀ ε > 0, ∀ n N,
      P.real {ω | ∃ k ≤ N, ε ≤ |S (n+k) ω-S n ω|} ≤ v n / ε^2) :
    ∀ᵐ ω ∂P, CauchySeq (fun n => S n ω) := by
  have hgood (ε : ℝ) (hε : 0 < ε) : ∀ᵐ ω ∂P, ∃ n, ∀ k, |S (n+k) ω-S n ω| < ε := by
    let B : Set Ω := {ω | ∀ n, ∃ k, ε ≤ |S (n+k) ω-S n ω|}
    have hb : ∀ n, P B ≤ ENNReal.ofReal (v n / ε^2) := by
      intro n
      have hsub : B ⊆ {ω | ∃ k, ε ≤ |S (n+k) ω-S n ω|} := fun ω hω => hω n
      exact (measure_mono hsub).trans
        (finite_maximum_to_all_indices P S n ε (v n / ε^2) (hmax ε hε n))
    have ht : Tendsto (fun n => ENNReal.ofReal (v n / ε^2)) atTop (𝓝 0) := by
      simpa only [zero_div,ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hv.div_const (ε^2))
    have hB : P B = 0 := le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb)) bot_le
    rw [ae_iff]
    convert hB using 2
    ext ω
    simp only [B,mem_setOf_eq,not_exists,not_forall,not_lt]
  have hall : ∀ᵐ ω ∂P, ∀ q : ℕ, ∃ n, ∀ k,
      |S (n+k) ω-S n ω| < 1/((q : ℝ)+1) :=
    ae_all_iff.mpr fun q => hgood _ (by positivity)
  filter_upwards [hall] with ω hω
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨q,hq⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨N,hN⟩ := hω q
  refine ⟨N,?_⟩
  intro i hi j hj
  have hi' := hN (i-N)
  have hj' := hN (j-N)
  rw [Nat.add_sub_of_le hi] at hi'
  rw [Nat.add_sub_of_le hj] at hj'
  rw [Real.dist_eq]
  have htri := abs_sub_le (S i ω) (S N ω) (S j ω)
  rw [abs_sub_comm (S N ω) (S j ω)] at htri
  exact htri.trans_lt (by linarith)
end Asakura.FullAudit
