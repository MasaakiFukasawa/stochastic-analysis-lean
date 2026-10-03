import Chapter3StoppedOrthogonality
import FullAuditMartingalePathNorm

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The exact finite L2 identity in prop:qcv, derived by expanding actual
integrable products. Orthogonality is needed only for distinct indices. -/
theorem orthogonal_sum_energy
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (s : Finset ι) (Z : ι → Ω → ℝ)
    (hZ : ∀ i ∈ s, MemLp (Z i) 2 P)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (∫ ω, Z i ω*Z j ω ∂P) = 0) :
    (∫ ω, (∑ i ∈ s, Z i ω)^2 ∂P) = ∑ i ∈ s, ∫ ω, Z i ω^2 ∂P := by
  have he (ω) : (∑ i ∈ s, Z i ω)^2 = ∑ i ∈ s, ∑ j ∈ s, Z i ω*Z j ω := by
    rw [pow_two,Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => Finset.mul_sum _ _ _
  have hp (i) (hi : i ∈ s) (j) (hj : j ∈ s) :
      Integrable (fun ω => Z i ω*Z j ω) P := (hZ i hi).integrable_mul (hZ j hj)
  simp_rw [he]
  rw [integral_finsetSum s (fun i hi => integrable_finsetSum s
    (fun j hj => hp i hi j hj))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum s (fun j hj => hp i hi j hj)]
  rw [Finset.sum_eq_single i]
  · simp only [pow_two]
  · intro j hj hji
    exact horth i hi j hj hji.symm
  · exact fun h => (h hi).elim

/-- Finite sums of the actual continuous M2 processes used in the discrete
quadratic-variation approximation stay in M2. -/
theorem finite_sum_m2
    {Ω ι : Type*} {m : MeasurableSpace Ω} [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (s : Finset ι) (Z : ι → ClosedTime T → Ω → ℝ)
    (hZ : ∀ i ∈ s, ContinuousM2Witness P F (Z i)) :
    ContinuousM2Witness P F (fun t ω => ∑ i ∈ s, Z i t ω) := by
  induction s using Finset.induction_on with
  | empty =>
    convert ContinuousM2Witness.zero P F using 1
    funext t ω
    simp
  | @insert a s ha ih =>
    have hs := ih (fun i hi => hZ i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.sum_insert ha,Pi.add_def] using
      (hZ a (Finset.mem_insert_self _ _)).add P F hs

/-- Doob's path supremum estimate for the finite martingale error sum.
The right hand side is its terminal L2 norm, as in the manuscript. -/
theorem finite_sum_doob
    {Ω ι : Type*} {m : MeasurableSpace Ω} [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (s : Finset ι) (Z : ι → ClosedTime T → Ω → ℝ)
    (hZ : ∀ i ∈ s, ContinuousM2Witness P F (Z i)) :
    let hS := finite_sum_m2 P F s Z hZ
    eLpNorm (continuousPath (fun t ω => ∑ i ∈ s, Z i t ω) hS.path) 2 P ≤
      2 * eLpNorm (fun ω => ∑ i ∈ s, Z i ⊤ ω) 2 P := by
  intro hS
  exact continuous_martingale_path_norm P F hF hle _ hS.adapted hS.moment hS.path hS.martingale

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.orthogonal_sum_energy
#print axioms Asakura.Chapter3Complete.finite_sum_m2
#print axioms Asakura.Chapter3Complete.finite_sum_doob
