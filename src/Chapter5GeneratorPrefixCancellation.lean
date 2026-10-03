import Chapter5GeneratorCancellation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem sum_integral_prefix_split
    {I : Type*} [Fintype I] (a b : ℝ) (ha : 0≤a) (hab : a≤b)
    (B : I → ℝ → ℝ) (hi : ∀ i,IntervalIntegrable (B i) volume 0 b) :
    (∑ i,∫ r in 0..b,B i r) = (∑ i,∫ r in 0..a,B i r)+(∑ i,∫ r in a..b,B i r) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((hi i).mono_set (by simpa only [uIcc_of_le ha,uIcc_of_le (ha.trans hab)] using Icc_subset_Icc_right hab))
    ((hi i).mono_set (by simpa only [uIcc_of_le hab,uIcc_of_le (ha.trans hab)] using Icc_subset_Icc_left ha))).symm

/-- If the generator vanishes only after the last observed time, its
two prefix integrals agree. Terms before that time cancel on subtraction. -/
theorem integrated_generator_prefix_cancellation
    (d : ℕ) (a b : ℝ) (ha : 0≤a) (hab : a≤b)
    (B : Fin d → ℝ → ℝ) (G : Fin d → Fin d → ℝ → ℝ)
    (hB : ∀ i,IntervalIntegrable (B i) volume 0 b)
    (hG : ∀ i j,IntervalIntegrable (G i j) volume 0 b)
    (hzero : ∀ r∈Icc a b,(∑ i,B i r)+(∑ i,∑ j,G i j r)/2=0) :
    (∑ i,∫ r in 0..b,B i r)+(∑ i,∑ j,∫ r in 0..b,G i j r)/2 =
      (∑ i,∫ r in 0..a,B i r)+(∑ i,∑ j,∫ r in 0..a,G i j r)/2 := by
  have hs : uIcc a b ⊆ uIcc 0 b := by
    simpa only [uIcc_of_le hab,uIcc_of_le (ha.trans hab)] using Icc_subset_Icc_left ha
  have hz := integrated_generator_cancellation_interval d a b hab B G
    (fun i => (hB i).mono_set hs) (fun i j => (hG i j).mono_set hs) hzero
  have hb := sum_integral_prefix_split a b ha hab B hB
  have hg : (∑ i,∑ j,∫ r in 0..b,G i j r) =
      (∑ i,∑ j,∫ r in 0..a,G i j r)+(∑ i,∑ j,∫ r in a..b,G i j r) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => sum_integral_prefix_split a b ha hab (G i) (hG i)
  linarith only [hz,hb,hg]

end Asakura.Chapter5
