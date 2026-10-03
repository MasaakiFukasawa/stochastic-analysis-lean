import Chapter2GridStieltjesEnergy
import Chapter2WeightedPaths

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 900000

/-- The cumulative mass of the actual Stieltjes measure is A(t)-A(a). -/
theorem interval_stieltjes_cumulative_real
    (a b : ℝ) (hab : a ≤ b) (A : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b))
    (hr : ∀ x ∈ Icc a b, ContinuousWithinAt A (Icc a b ∩ Ici x) x)
    (t : ℝ) (ht : t ∈ Icc a b) :
    (intervalStieltjes a b hab A hA hr).measure.real (Iic t) = A t-A a := by
  rw [Measure.real,StieltjesFunction.measure_Iic _
    (interval_stieltjes_left_limit a b hab (fun _ : Unit => A) (fun _ => hA) (fun _ => hr) ())]
  change (ENNReal.ofReal (A (intervalClamp a b hab t)-A a)).toReal = A t-A a
  rw [intervalClamp_eq a b hab ht,ENNReal.toReal_ofReal]
  exact sub_nonneg.2 (hA (left_mem_Icc.2 hab) ht ht.1)

/-- The elementary energy is expressed using the original increasing
process A, rather than an unidentified cumulative measure. -/
theorem actual_stieltjes_grid_energy
    (a b : ℝ) (hab : a ≤ b) (A : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b)) (hc : ContinuousOn A (Icc a b))
    (N : ℕ) (u : ℕ → ℝ) (hu : StrictMonoOn u (Iic N))
    (huab : ∀ j ≤ N, u j ∈ Icc a b) (G : ℕ → ℝ)
    (t : ℝ) (ht : t ∈ Icc a b) :
    (∫ r in Iic t,
      (∑ j ∈ Finset.range N, (Ico (u j) (u (j+1))).indicator (fun _ => G j) r)^2
        ∂(intervalStieltjes a b hab A hA (fun x hx => (hc x hx).mono inter_subset_left)).measure) =
    ∑ j ∈ Finset.range N, G j^2 * stepIncrement (u j) (u (j+1)) A t := by
  let hr := fun x (hx : x ∈ Icc a b) => (hc x hx).mono (inter_subset_left (t := Ici x))
  let μ := (intervalStieltjes a b hab A hA hr).measure
  letI : IsFiniteMeasure μ := intervalStieltjes_finite a b hab A hA hr
  letI : NullSingletonClass μ := interval_stieltjes_no_atoms_on a b hab A hA hr hc
  have he := grid_stieltjes_square_integral μ N u hu G t
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < N := Finset.mem_range.1 hj
  have hmin (k : ℕ) (hk : k ≤ N) : min (u k) t ∈ Icc a b :=
    ⟨le_min (huab k hk).1 ht.1,(min_le_right _ _).trans ht.2⟩
  dsimp only [stepIncrement]
  rw [interval_stieltjes_cumulative_real a b hab A hA hr _ (hmin (j+1) (by omega)),
    interval_stieltjes_cumulative_real a b hab A hA hr _ (hmin j hjn.le)]
  ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.interval_stieltjes_cumulative_real
#print axioms Asakura.Chapter2Complete.actual_stieltjes_grid_energy
