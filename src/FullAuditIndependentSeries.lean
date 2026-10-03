import FullAuditMaximalCauchy

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- Reindexing is explicit, so the maximal inequality can be applied to every tail. -/
theorem partial_sum_tail_identity {Ω : Type*} (Z : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) :
    partialSum (fun i => Z (i+n)) k ω = partialSum Z (n+k) ω-partialSum Z n ω := by
  simp only [partialSum]
  rw [Finset.sum_range_add]
  simp only [Nat.add_comm n,add_sub_cancel_left]

/-- The second part of the exercise, using the maximal inequality, continuity
 from below and countably many positive error thresholds. -/
theorem independent_series_ae_cauchy_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hm : ∀ i, Measurable[m] (Z i)) (hi : iIndepFun Z P)
    (h2 : ∀ i, MemLp (Z i) 2 P) (hz : ∀ i, ∫ ω, Z i ω ∂P = 0)
    (hsum : Summable (fun i => ∫ ω, (Z i ω)^2 ∂P)) :
    ∀ᵐ ω ∂P, CauchySeq (fun n => partialSum Z n ω) := by
  let v : ℕ → ℝ := fun n => ∑' i, ∫ ω, (Z (i+n) ω)^2 ∂P
  have hv : Tendsto v atTop (𝓝 0) := tendsto_sum_nat_add (fun i => ∫ ω, (Z i ω)^2 ∂P)
  apply maximal_tail_ae_cauchy P (partialSum Z) v hv
  intro ε hε n N
  have hind : iIndepFun (fun i => Z (i+n)) P := hi.precomp (fun _ _ h => Nat.add_right_cancel h)
  have hmax := kolmogorov_maximal_written P (fun i => Z (i+n))
    (fun i => hm (i+n)) hind (fun i => h2 (i+n)) (fun i => hz (i+n)) N ε hε
  simp_rw [partial_sum_tail_identity] at hmax
  have he := independent_sum_square_energy P (fun i => Z (i+n))
    (fun i => hm (i+n)) hind (fun i => h2 (i+n)) (fun i => hz (i+n)) N
  simp_rw [partial_sum_tail_identity] at he
  rw [he] at hmax
  have htail : Summable (fun i => ∫ ω, (Z (i+n) ω)^2 ∂P) := (summable_nat_add_iff n).mpr hsum
  have hb : (∑ i ∈ Finset.range N, ∫ ω, (Z (i+n) ω)^2 ∂P) ≤ v n :=
    htail.sum_le_tsum (Finset.range N) (fun i _ => integral_nonneg (fun ω => sq_nonneg _))
  exact hmax.trans (div_le_div_of_nonneg_right hb (sq_nonneg ε))

theorem independent_series_ae_converges_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hm : ∀ i, Measurable[m] (Z i)) (hi : iIndepFun Z P)
    (h2 : ∀ i, MemLp (Z i) 2 P) (hz : ∀ i, ∫ ω, Z i ω ∂P = 0)
    (hsum : Summable (fun i => ∫ ω, (Z i ω)^2 ∂P)) :
    ∀ᵐ ω ∂P, ∃ l : ℝ, Tendsto (fun n => partialSum Z n ω) atTop (𝓝 l) := by
  filter_upwards [independent_series_ae_cauchy_written P Z hm hi h2 hz hsum] with ω hω
  exact cauchySeq_tendsto_of_complete hω
end Asakura.FullAudit
