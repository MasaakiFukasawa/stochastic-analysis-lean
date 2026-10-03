import Appendix
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace Asakura

/-- The manuscript's counting function; no finiteness or sigma-finiteness of μ. -/
theorem written_counting_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n)) :
    (∫⁻ ω, ∑' n, (A n).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ) = ∑' n, μ (A n) := by
  rw [lintegral_tsum (fun n => (measurable_const.indicator (hA n)).aemeasurable)]
  congr 1
  funext n
  simp [lintegral_indicator (hA n)]

/-- Finite integral makes the counting function finite almost everywhere;
its value counts exactly the sets containing the point. -/
theorem written_borel_cantelli {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (hfinite : ∑' n, μ (A n) < ∞) :
    ∀ᵐ ω ∂μ, {n | ω ∈ A n}.Finite := by
  have hm : Measurable (fun ω => ∑' n, (A n).indicator (fun _ => (1 : ℝ≥0∞)) ω) :=
    Measurable.ennreal_tsum (fun n => measurable_const.indicator (hA n))
  have hi : (∫⁻ ω, ∑' n, (A n).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ) ≠ ∞ := by
    rw [written_counting_integral μ A hA]
    exact hfinite.ne
  filter_upwards [ae_lt_top hm hi] with ω hω
  have hf := ENNReal.finite_const_le_of_tsum_ne_top hω.ne (by norm_num : (1 : ℝ≥0∞) ≠ 0)
  apply hf.subset
  intro n hn
  change ω ∈ A n at hn
  change 1 ≤ (A n).indicator (fun _ => (1 : ℝ≥0∞)) ω
  rw [Set.indicator_of_mem hn]



/-- The literal limsup-set conclusion printed in the appendix. -/
theorem written_borel_cantelli_limsup {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (hfinite : ∑' n, μ (A n) < ∞) :
    μ (⋂ m : ℕ, ⋃ n ≥ m, A n) = 0 := by
  have hn : ∀ᵐ ω ∂μ, ω ∉ (⋂ m : ℕ, ⋃ n ≥ m, A n) := by
    filter_upwards [written_borel_cantelli μ A hA hfinite] with ω hω
    intro hmem
    obtain ⟨b, hb⟩ := hω.bddAbove
    have hex : ∃ n, b+1 ≤ n ∧ ω ∈ A n := by
      simpa only [mem_iUnion, exists_prop] using mem_iInter.mp hmem (b+1)
    obtain ⟨n, hn, hAn⟩ := hex
    have hnb : n ≤ b := hb hAn
    omega
  simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hn

end Asakura
