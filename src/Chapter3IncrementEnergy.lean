import Chapter3IncrementProcess
import Chapter2LocalQuadraticVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Zero initial M2 martingales have zero mean at every time, directly from
conditional expectation. -/
theorem m2_mean_zero
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hle : ∀ t, F t ≤ m)
    (Y : ClosedTime T → Ω → ℝ) (hY : ContinuousM2Witness P F Y) (t : ClosedTime T) :
    (∫ ω, Y t ω ∂P) = 0 := by
  have h := integral_congr_ae ((hY.martingale ⊥ t bot_le).trans hY.initial)
  rw [integral_condExp (hle ⊥)] at h
  simpa only [Pi.zero_apply,integral_zero] using h

/-- Integrability of the compensating increment and the increment-energy
identity follow from the square-defect martingale; they are not assumed. -/
theorem increment_energy_of_square_defect
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hle : ∀ t, F t ≤ m)
    (D A : ClosedTime T → Ω → ℝ) (hD : ∀ t, MemLp (D t) 2 P)
    (hR : ContinuousM2Witness P F (fun t ω => D t ω^2-A t ω)) (t : ClosedTime T) :
    Integrable (A t) P ∧ (∫ ω, D t ω^2 ∂P) = ∫ ω, A t ω ∂P := by
  have hsq := (memLp_two_iff_integrable_sq (hD t).aestronglyMeasurable).mp (hD t)
  have hr := (hR.moment t).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have ha : Integrable (A t) P := by
    convert hsq.sub hr using 1
    funext ω
    simp only [Pi.sub_apply,sub_sub_cancel]
  have hz := m2_mean_zero P F hle _ hR t
  rw [integral_sub hsq ha] at hz
  exact ⟨ha,sub_eq_zero.mp hz⟩

/-- A finite sum of compensator increments telescopes exactly, with no
assumption about strictness of the stopping partition. -/
theorem finite_increment_telescoping {ι : Type*} (q : ι → ℝ) (τ : ℕ → ι) (N : ℕ) :
    (∑ j ∈ Finset.range N, (q (τ (j+1))-q (τ j))) = q (τ N)-q (τ 0) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih]; ring

/-- After localization, the finite total error energy is controlled by the
expected quadratic variation at the deterministic endpoint. -/
theorem sum_increment_energies_le
    {Ω ι : Type*} [MeasurableSpace Ω] [LinearOrder ι] [OrderBot ι]
    (P : Measure Ω) (Q : ι → Ω → ℝ) (τ : ℕ → Ω → ι)
    (hτ0 : ∀ ω, τ 0 ω = ⊥)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun s => Q s ω))
    (hzero : Q ⊥ =ᵐ[P] 0) (t : ι) (hiQ : Integrable (Q t) P)
    (hi : ∀ j, Integrable (fun ω => Q (min (τ (j+1) ω) t) ω-Q (min (τ j ω) t) ω) P)
    (e : ℕ → ℝ)
    (he : ∀ j, e j = ∫ ω, Q (min (τ (j+1) ω) t) ω-Q (min (τ j ω) t) ω ∂P)
    (N : ℕ) : (∑ j ∈ Finset.range N, e j) ≤ ∫ ω, Q t ω ∂P := by
  simp_rw [he]
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  apply integral_mono_ae (integrable_finsetSum _ (fun j _ => hi j)) hiQ
  filter_upwards [hmono,hzero] with ω hm hz
  rw [finite_increment_telescoping (fun s => Q s ω) (fun j => min (τ j ω) t) N]
  simp only [hτ0,min_bot_left,hz,Pi.zero_apply,sub_zero]
  exact hm (min_le_right _ _)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.m2_mean_zero
#print axioms Asakura.Chapter3Complete.increment_energy_of_square_defect
#print axioms Asakura.Chapter3Complete.finite_increment_telescoping
#print axioms Asakura.Chapter3Complete.sum_increment_energies_le
