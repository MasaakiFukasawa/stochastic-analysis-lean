import Chapter2LocalCovarianceCS

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The one-sided stopping identity in the exercise after Ito isometry.
Constancy after the stopping time is derived from the interval KW inequality,
not assumed as a covariation rule. -/
theorem local_covariance_one_sided_stopping
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y C D : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hD : LocalCovarianceWitness P F (fun t ω => X (min (τ ω) t) ω) Y D) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → D t ω = C (min (τ ω) t) ω := by
  obtain ⟨A,hA⟩ := local_covariance_witness_exists P F hF hle hnull X X hX hX
  obtain ⟨B,hB⟩ := local_covariance_witness_exists P F hF hle hnull Y Y hY hY
  have hXs := hX.stopped P F hF hle τ hτ
  have hAs := hA.stopped P F hF hle τ hτ
  have hDs : LocalCovarianceWitness P F (fun t ω => X (min (τ ω) t) ω)
      (fun t ω => Y (min (τ ω) t) ω) (fun t ω => D (min (τ ω) t) ω) := by
    simpa only [← min_assoc,min_self] using hD.stopped P F hF hle τ hτ
  have he := hDs.unique P F hF hle (hC.stopped P F hF hle τ hτ)
  have hkw := local_covariance_interval_cs P F hF hle hnull
    (fun t ω => X (min (τ ω) t) ω) Y (fun t ω => A (min (τ ω) t) ω) B D hXs hY hAs hB hD
  filter_upwards [he,hkw] with ω heω hkwω
  intro t ht
  have hd := hkwω (min (τ ω) t) t (min_le_right _ _) ht
  change |D t ω-D (min (τ ω) t) ω| ≤
    Real.sqrt (A (min (τ ω) t) ω-A (min (τ ω) (min (τ ω) t)) ω)*
      Real.sqrt (B t ω-B (min (τ ω) t) ω) at hd
  simp only [← min_assoc,min_self,sub_self,Real.sqrt_zero,zero_mul] at hd
  have heq : D t ω = D (min (τ ω) t) ω := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd (abs_nonneg _)))
  exact heq.trans (heω t ht)

/-- Both one-sided formulas and the double-stopped formula, on a common
sample null set. The right-sided formula uses proved symmetry. -/
theorem local_covariance_stopping_exercise
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y C D E G : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hD : LocalCovarianceWitness P F (fun t ω => X (min (τ ω) t) ω) Y D)
    (hE : LocalCovarianceWitness P F X (fun t ω => Y (min (τ ω) t) ω) E)
    (hG : LocalCovarianceWitness P F (fun t ω => X (min (τ ω) t) ω)
      (fun t ω => Y (min (τ ω) t) ω) G) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → G t ω = C (min (τ ω) t) ω ∧
      D t ω = C (min (τ ω) t) ω ∧ E t ω = C (min (τ ω) t) ω := by
  filter_upwards [local_covariance_stopping P F hF hle hC τ hτ hG,
    local_covariance_one_sided_stopping P F hF hle hnull X Y C D hX hY hC τ hτ hD,
    local_covariance_one_sided_stopping P F hF hle hnull Y X C E hY hX (hC.symm P F) τ hτ (hE.symm P F)]
    with ω hg hd he
  exact fun t ht => ⟨hg t ht,hd t ht,he t ht⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_covariance_stopping_exercise
