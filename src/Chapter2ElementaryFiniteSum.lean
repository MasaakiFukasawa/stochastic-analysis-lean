import Chapter2ElementaryLocalCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)

include hF hle

/-- Finite sums preserve the actual local-martingale characterization,
allowing a different localizing sequence for every summand. -/
theorem local_process_finset_sum {ι : Type*} (s : Finset ι)
    (Z : ι → ClosedTime T → Ω → ℝ)
    (hZ : ∀ i ∈ s, LocalMProcessWitness P F (Z i))
    (hzero : LocalMProcessWitness P F (fun _ _ => 0)) :
    LocalMProcessWitness P F (fun t ω => ∑ i ∈ s, Z i t ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hzero
  | @insert i s hi ih =>
    have h := (hZ i (Finset.mem_insert_self _ _)).add P F hF hle
      (ih (fun j hj => hZ j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

/-- Finite sums of covariations satisfy the defining local-martingale
and finite-variation conditions, rather than an assumed bilinearity rule. -/
theorem local_covariance_finset_sum {ι : Type*} (s : Finset ι)
    (Z D : ι → ClosedTime T → Ω → ℝ) (Y : ClosedTime T → Ω → ℝ)
    (hD : ∀ i ∈ s, LocalCovarianceWitness P F (Z i) Y (D i))
    (hzero : LocalCovarianceWitness P F (fun _ _ => 0) Y (fun _ _ => 0)) :
    LocalCovarianceWitness P F (fun t ω => ∑ i ∈ s, Z i t ω) Y
      (fun t ω => ∑ i ∈ s, D i t ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hzero
  | @insert i s hi ih =>
    have h := (hD i (Finset.mem_insert_self _ _)).bilinear P F hF hle
      (ih (fun j hj => hD j (Finset.mem_insert_of_mem hj))) 1
    simpa only [one_mul,Finset.sum_insert hi] using h

/-- The elementary integral associated to any finite representation is
an actual local martingale and its actual covariation is the sum of the
Stieltjes increments. No common localizer is assumed for the summands. -/
theorem finite_elementary_integral_covariance
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    {ι : Type*} (s : Finset ι) (a b : ι → ClosedTime T) (G : ι → Ω → ℝ)
    (hab : ∀ i, a i ≤ b i) (hGm : ∀ i, Measurable[F (a i)] (G i))
    (hG : ∀ i, MemLp (G i) ∞ P) :
    let Z := fun t ω => ∑ i ∈ s, G i ω * (X (min (b i) t) ω-X (min (a i) t) ω)
    LocalMProcessWitness P F Z ∧ ∃ D, LocalCovarianceWitness P F Z Y D ∧
      ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
        D t ω = ∑ i ∈ s, G i ω * (C (min (b i) t) ω-C (min (a i) t) ω) := by
  classical
  let Z := fun i t ω => G i ω * (X (min (b i) t) ω-X (min (a i) t) ω)
  have hz i : LocalMProcessWitness P F (Z i) :=
    elementary_integral_local_martingale P F hF hle X hX (a i) (b i) (hab i) (G i) (hGm i) (hG i)
  have h0 : LocalMProcessWitness P F (fun _ _ => 0) := by
    simpa only [zero_mul] using hX.smul P F 0
  have hc0 : LocalCovarianceWitness P F (fun _ _ => 0) Y (fun _ _ => 0) := by
    refine ⟨?_,?_⟩
    · simpa only [zero_mul,sub_zero] using h0
    · simpa only [zero_mul] using hC.variation.smul F 0
  choose D hD using fun i => local_covariance_witness_exists P F hF hle hnull (Z i) Y (hz i) hY
  refine ⟨local_process_finset_sum P F hF hle s Z (fun i _ => hz i) h0,
    (fun t ω => ∑ i ∈ s, D i t ω),
    local_covariance_finset_sum P F hF hle s Z D Y (fun i _ => hD i) hc0,?_⟩
  have he i := elementary_local_integral_covariance P F hF hle hnull X Y C hX hY hC
    (a i) (b i) (hab i) (G i) (hGm i) (hG i) (D i) (hD i)
  have he' : ∀ᵐ ω ∂P, ∀ i ∈ s, ∀ t, t < ⊤ →
      D i t ω = G i ω * (C (min (b i) t) ω-C (min (a i) t) ω) :=
    (ae_ball_iff s.finite_toSet.countable).2 (fun i _ => he i)
  filter_upwards [he'] with ω hω
  intro t ht
  exact Finset.sum_congr rfl (fun i hi => hω i hi t ht)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_process_finset_sum
#print axioms Asakura.Chapter2Complete.local_covariance_finset_sum
#print axioms Asakura.Chapter2Complete.finite_elementary_integral_covariance
