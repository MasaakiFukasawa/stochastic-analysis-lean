import Chapter2StepEnergyAlgebra
import Chapter2ElementaryFiniteSum

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- For an elementary strategy on an ordered common grid, the actual
quadratic variation of its Ito integral is the square-coefficient energy
sum. Both required covariations are constructed, and the cross terms are
removed by the checked finite-grid algebra. -/
theorem elementary_grid_quadratic_variation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (N : ℕ) (u : ℕ → ClosedTime T) (hu : StrictMonoOn u (Iic N))
    (G : ℕ → Ω → ℝ) (hGm : ∀ i < N, Measurable[F (u i)] (G i))
    (hG : ∀ i < N, MemLp (G i) ∞ P) :
    let Z := fun t ω => ∑ i ∈ Finset.range N, G i ω * stepIncrement (u i) (u (i+1)) (fun t => X t ω) t
    LocalMProcessWitness P F Z ∧ ∃ Q, LocalCovarianceWitness P F Z Z Q ∧
      ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
        Q t ω = ∑ i ∈ Finset.range N, G i ω ^ 2 * stepIncrement (u i) (u (i+1)) (fun t => A t ω) t := by
  classical
  let Z := fun t ω => ∑ i ∈ Finset.range N, G i ω * stepIncrement (u i) (u (i+1)) (fun t => X t ω) t
  have hab (i : Fin N) : u i.val ≤ u (i.val+1) :=
    hu.monotoneOn i.isLt.le (show i.val+1 ∈ Iic N by change i.val+1 ≤ N; omega) (by omega)
  have hfirst := finite_elementary_integral_covariance P F hF hle hnull X X A hX hX hA
    (Finset.univ : Finset (Fin N)) (fun i => u i.val) (fun i => u (i.val+1)) (fun i => G i.val)
    hab (fun i => hGm i.val i.isLt) (fun i => hG i.val i.isLt)
  have hsX (t : ClosedTime T) (ω : Ω) := Fin.sum_univ_eq_sum_range
    (fun i => G i ω*(X (min (u (i+1)) t) ω-X (min (u i) t) ω)) N
  have hsA (t : ClosedTime T) (ω : Ω) := Fin.sum_univ_eq_sum_range
    (fun i => G i ω*(A (min (u (i+1)) t) ω-A (min (u i) t) ω)) N
  simp only [hsX,hsA] at hfirst
  change LocalMProcessWitness P F Z ∧ ∃ D, LocalCovarianceWitness P F Z X D ∧
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → D t ω = ∑ i ∈ Finset.range N,
      G i ω * stepIncrement (u i) (u (i+1)) (fun t => A t ω) t at hfirst
  obtain ⟨hZ,D,hD,hDid⟩ := hfirst
  have hsecond := finite_elementary_integral_covariance P F hF hle hnull X Z D hX hZ (hD.symm P F)
    (Finset.univ : Finset (Fin N)) (fun i => u i.val) (fun i => u (i.val+1)) (fun i => G i.val)
    hab (fun i => hGm i.val i.isLt) (fun i => hG i.val i.isLt)
  have hsD (t : ClosedTime T) (ω : Ω) := Fin.sum_univ_eq_sum_range
    (fun i => G i ω*(D (min (u (i+1)) t) ω-D (min (u i) t) ω)) N
  simp only [hsX,hsD] at hsecond
  change LocalMProcessWitness P F Z ∧ ∃ Q, LocalCovarianceWitness P F Z Z Q ∧
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → Q t ω = ∑ i ∈ Finset.range N,
      G i ω * stepIncrement (u i) (u (i+1)) (fun t => D t ω) t at hsecond
  obtain ⟨_,Q,hQ,hQid⟩ := hsecond
  refine ⟨hZ,Q,hQ,?_⟩
  filter_upwards [hDid,hQid] with ω hd hq
  intro t ht
  rw [hq t ht]
  calc
    _ = ∑ i ∈ Finset.range N, G i ω * stepIncrement (u i) (u (i+1))
        (fun r => ∑ j ∈ Finset.range N, G j ω * stepIncrement (u j) (u (j+1)) (fun t => A t ω) r) t := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [stepIncrement]
      rw [hd (min (u (i+1)) t) ((min_le_right _ _).trans_lt ht),
        hd (min (u i) t) ((min_le_right _ _).trans_lt ht)]
      rfl
    _ = _ := grid_square_energy_identity N u hu (fun i => G i ω) (fun t => A t ω) t

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.elementary_grid_quadratic_variation
