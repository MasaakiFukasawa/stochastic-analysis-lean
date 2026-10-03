import Chapter4AdaptedPicardLimit
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's Fatou step: the already constructed almost surely
uniform path limit is also the L2 limit. No L2 convergence of that limit
is assumed. The upper bound is the tail of the increment norms. -/
theorem picard_fatou_tail
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (Z : ℕ → Ω → E) (hZ : ∀ n, AEStronglyMeasurable (Z n) P)
    (Y : Ω → E) (hY : AEStronglyMeasurable Y P)
    (hs : (∑' n, eLpNorm (Z n) 2 P) ≠ ∞)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range n, Z k ω) atTop (𝓝 (Y ω))) :
    MemLp Y 2 P ∧
    (∀ n, eLpNorm (fun ω => Y ω-∑ k ∈ Finset.range n, Z k ω) 2 P ≤
      ∑' k, eLpNorm (Z (k+n)) 2 P) ∧
    Tendsto (fun n => eLpNorm (fun ω => Y ω-∑ k ∈ Finset.range n, Z k ω) 2 P) atTop (𝓝 0) := by
  let S := fun n ω => ∑ k ∈ Finset.range n, Z k ω
  have hm n : AEStronglyMeasurable (S n) P := by
    apply (Finset.aestronglyMeasurable_sum (Finset.range n) (fun k _ => hZ k)).congr
    exact Filter.Eventually.of_forall (fun ω => by simp [S])
  have hb (n : ℕ) : eLpNorm (fun ω => Y ω-S n ω) 2 P ≤ ∑' k, eLpNorm (Z (k+n)) 2 P := by
    have hconv : ∀ᵐ ω ∂P, Tendsto (fun m => S (m+n) ω-S n ω) atTop (𝓝 (Y ω-S n ω)) := by
      filter_upwards [hlim] with ω hω
      exact (hω.comp (tendsto_add_atTop_nat n)).sub tendsto_const_nhds
    apply (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun m => (hm (m+n)).sub (hm n)) _
      (hY.sub (hm n)) hconv).trans
    apply liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro m
    have he : (fun ω => S (m+n) ω-S n ω) = ∑ k ∈ Finset.range m, Z (k+n) := by
      funext ω
      simp only [S,Finset.sum_apply]
      rw [Nat.add_comm m n,Finset.sum_range_add]
      simp only [Nat.add_comm n,add_sub_cancel_left]
    change eLpNorm (fun ω => S (m+n) ω-S n ω) 2 P ≤ _
    rw [he]
    exact (eLpNorm_sum_le (by norm_num : (1:ℝ≥0∞) ≤ 2)).trans (ENNReal.sum_le_tsum _)
  have ht := ENNReal.tendsto_sum_nat_add (fun n => eLpNorm (Z n) 2 P) hs
  have hi : MemLp Y 2 P := by
    have h0 := hb 0
    simp only [S,Finset.range_zero,Finset.sum_empty,sub_zero,Nat.add_zero] at h0
    exact h0.trans_lt hs.lt_top
  exact ⟨hi,hb,tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hb⟩

/-- Combine the pathwise construction with the Fatou argument for the
actual factorial bounds of the Picard iteration. -/
theorem adapted_picard_series_L2_limit
    {Ω D : Type*} {m : MeasurableSpace Ω}
    [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : D → MeasurableSpace Ω)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z : ℕ → Ω → C(D,ℝ)) (hZ : ∀ n, Measurable[m] (Z n))
    (ha : ∀ n t, Measurable[F t] (fun ω => Z n ω t))
    (A a : ℝ) (ha0 : 0 ≤ a)
    (hb : ∀ n, eLpNorm (Z n) 2 P ≤ ENNReal.ofReal (A*Real.sqrt (a^n/(n.factorial:ℝ)))) :
    ∃ Y : Ω → C(D,ℝ), Measurable[m] Y ∧
      (∀ t, Measurable[F t] (fun ω => Y ω t)) ∧ MemLp Y 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range n, Z k ω) atTop (𝓝 (Y ω))) ∧
      Tendsto (fun n => eLpNorm (fun ω => Y ω-∑ k ∈ Finset.range n, Z k ω) 2 P) atTop (𝓝 0) := by
  obtain ⟨Y,hYm,hYa,hlim⟩ := adapted_picard_series_limit P F hnull Z hZ ha A a ha0 hb
  have hsum := ((summable_sqrt_factorial a ha0).mul_left A).tsum_ofReal_lt_top
  have hs : (∑' n, eLpNorm (Z n) 2 P) ≠ ∞ :=
    ((ENNReal.tsum_le_tsum hb).trans_lt hsum).ne
  have hf := picard_fatou_tail P Z (fun n => (hZ n).aestronglyMeasurable) Y hYm.aestronglyMeasurable hs hlim
  exact ⟨Y,hYm,hYa,hf.1,hlim,hf.2.2⟩

end Asakura.Chapter4
