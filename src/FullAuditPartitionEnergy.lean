import FullAuditQuadraticPartition

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- At a partition point, later terms in the printed finite square sum vanish. -/
theorem partition_squares_at_point {Ω ι : Type*} [LinearOrder ι]
    (X : ι → Ω → ℝ) (π : ℕ → ι) (hπ : Monotone π)
    (N k : ℕ) (hk : k ≤ N) (ω : Ω) :
    partitionSquares X π N (π k) ω =
      ∑ j ∈ Finset.range k, (X (π (j+1)) ω-X (π j) ω)^2 := by
  unfold partitionSquares
  calc
    _ = ∑ j ∈ Finset.range k, (X (min (π k) (π (j+1))) ω-X (min (π k) (π j)) ω)^2 := by
      apply Eq.symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro j hjN hjk
      have hkj : k ≤ j := Nat.le_of_not_gt (fun h => hjk (Finset.mem_range.mpr h))
      simp only [min_eq_left (hπ hkj),min_eq_left (hπ (hkj.trans (Nat.le_succ j))),sub_self,zero_pow (by decide : 2 ≠ 0)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjk := Finset.mem_range.mp hj
      rw [min_eq_right (hπ (Nat.succ_le_of_lt hjk)),min_eq_right (hπ hjk.le)]

/-- The increment of Y=X²-Q at consecutive partition points is exactly 2XΔX. -/
theorem square_defect_partition_increment {Ω ι : Type*} [LinearOrder ι]
    (X : ι → Ω → ℝ) (π : ℕ → ι) (hπ : Monotone π)
    (N j : ℕ) (hj : j < N) (ω : Ω) :
    (X (π (j+1)) ω ^ 2-partitionSquares X π N (π (j+1)) ω) -
      (X (π j) ω ^ 2-partitionSquares X π N (π j) ω) =
      2 * X (π j) ω * (X (π (j+1)) ω-X (π j) ω) := by
  rw [partition_squares_at_point X π hπ N (j+1) (Nat.succ_le_of_lt hj),
    partition_squares_at_point X π hπ N j hj.le,Finset.sum_range_succ]
  ring

/-- The square sum is zero at the initial time, without requiring a strict partition. -/
theorem partition_squares_initial {Ω ι : Type*} [LinearOrder ι] [OrderBot ι]
    (X : ι → Ω → ℝ) (π : ℕ → ι) (N : ℕ) : partitionSquares X π N ⊥ = 0 := by
  funext ω
  simp [partitionSquares,min_eq_left bot_le]

/-- Apply the checked partition martingale lemma at the initial and terminal
 times and integrate, yielding precisely E Q = E X_T². -/
theorem partition_square_energy_written {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ι → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t)) (h2 : ∀ t, MemLp (X t) 2 P)
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (hz : X ⊥ =ᵐ[P] 0) (π : ℕ → ι) (hπ : Monotone π) (h0 : π 0 = ⊥) (N : ℕ) (hN : π N = ⊤) :
    (∫ ω, partitionSquares X π N ⊤ ω ∂P) = ∫ ω, X ⊤ ω ^ 2 ∂P := by
  have he := partition_square_martingale_written P F hF hle X hm h2 hmart π hπ h0 N hN ⊥ ⊤ bot_le
  have hinit : (fun ω => X ⊥ ω ^ 2-partitionSquares X π N ⊥ ω) =ᵐ[P] 0 := by
    filter_upwards [hz] with ω hω
    simp [partition_squares_initial,hω]
  have h := integral_congr_ae (he.trans hinit)
  rw [integral_condExp (hle ⊥),integral_sub
    ((memLp_two_iff_integrable_sq (h2 ⊤).aestronglyMeasurable).mp (h2 ⊤))
    (partition_squares_integrable P X h2 π N ⊤)] at h
  simp only [Pi.zero_apply,integral_zero] at h
  linarith

/-- Every term remains essentially bounded in the finite square formula. -/
theorem partition_defect_memLp_top {Ω ι : Type*} [MeasurableSpace Ω] [LinearOrder ι]
    (P : Measure Ω) (X : ι → Ω → ℝ) (hTop : ∀ t, MemLp (X t) ∞ P)
    (π : ℕ → ι) (N : ℕ) (t : ι) :
    MemLp (fun ω => X t ω ^ 2-partitionSquares X π N t ω) ∞ P := by
  have hsq (u : ι) : MemLp (fun ω => X u ω ^ 2) ∞ P := by
    simpa only [Pi.mul_def,pow_two] using (hTop u).mul (hTop u) (r := ∞)
  have hQ : MemLp (partitionSquares X π N t) ∞ P := by
    apply memLp_finset_sum
    intro j hj
    have hd := (hTop (min t (π (j+1)))).sub (hTop (min t (π j)))
    simpa only [Pi.mul_def,Pi.sub_apply,pow_two] using hd.mul hd (r := ∞)
  exact (hsq t).sub hQ

end Asakura.FullAudit
