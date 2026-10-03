import Chapter3SignedStieltjesApproximation
import Chapter3WrittenTaylor

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Every actual stopped partition sum is bounded by path total variation. -/
theorem stopped_partition_variation_bound
    {ι : Type*} [LinearOrder ι] (A : ι → ℝ) (b : ι)
    (hA : BoundedVariationOn A (Iic b)) (τ : ℕ → ι) (hτ : Monotone τ)
    (t : ι) (N : ℕ) :
    (∑ j ∈ Finset.range N, |A (min (τ (j+1)) (min b t))-A (min (τ j) (min b t))|) ≤
      (eVariationOn A (Iic b)).toReal := by
  have he := eVariationOn.sum_le (f := A) (n := N)
    (hτ.min monotone_const |>.min monotone_const)
    (fun i => show min (min (τ i) b) t ∈ Iic b from (min_le_left _ _).trans (min_le_right _ _))
  simp only [min_assoc,edist_eq_enorm_sub,← ofReal_norm,Real.norm_eq_abs] at he
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)] at he
  have h := ENNReal.toReal_mono hA he
  simpa only [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] using h

/-- A finite-variation factor and an oscillation-controlled factor give
a uniform bound for the actual infinite weighted cross sum. -/
theorem variation_cross_sum_bound
    {T : EReal} [Fact (0 ≤ T)] (A B H : ClosedTime T → ℝ)
    (b : ClosedTime T) (hb : b < ⊤) (hA : BoundedVariationOn A (Iic b))
    (τ : ℕ → ClosedTime T) (hτ : Monotone τ) (hco : ∀ t, t < ⊤ → ∃ N, t < τ N)
    (K δ : ℝ) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hH : ∀ s, s ≤ b → |H s| ≤ K)
    (hB : ∀ j t, |B (min (τ (j+1)) t)-B (min (τ j) t)| ≤ δ)
    (t : ClosedTime T) :
    |∑' j, H (τ j)*(A (min (τ (j+1)) (min b t))-A (min (τ j) (min b t)))*
      (B (min (τ (j+1)) (min b t))-B (min (τ j) (min b t)))| ≤
      K*δ*(eVariationOn A (Iic b)).toReal := by
  obtain ⟨N,hN⟩ := hco b hb
  have hs : (∑' j, H (τ j)*(A (min (τ (j+1)) (min b t))-A (min (τ j) (min b t)))*
      (B (min (τ (j+1)) (min b t))-B (min (τ j) (min b t)))) =
      ∑ j ∈ Finset.range N, H (τ j)*(A (min (τ (j+1)) (min b t))-A (min (τ j) (min b t)))*
      (B (min (τ (j+1)) (min b t))-B (min (τ j) (min b t))) := by
    apply tsum_eq_sum
    intro j hj
    have htj := (min_le_left b t).trans (hN.le.trans (hτ (Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h)))))
    rw [min_eq_right htj,min_eq_right (htj.trans (hτ (Nat.le_succ j))),sub_self,mul_zero,zero_mul]
  rw [hs]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range N, K*δ*|A (min (τ (j+1)) (min b t))-A (min (τ j) (min b t))| := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hjb : τ j ≤ b
      · rw [abs_mul,abs_mul]
        have h := mul_le_mul (hH _ hjb) (hB j (min b t)) (abs_nonneg _) hK
        have hh := mul_le_mul_of_nonneg_right h
          (abs_nonneg (A (min (τ (j+1)) (min b t))-A (min (τ j) (min b t))))
        nlinarith
      · have htj := (min_le_left b t).trans (le_of_not_ge hjb)
        simp only [min_eq_right htj,min_eq_right (htj.trans (hτ (Nat.le_succ j))),sub_self,mul_zero,zero_mul,abs_zero,le_refl]
    _ = K*δ*∑ j ∈ Finset.range N, |A (min (τ (j+1)) (min b t))-A (min (τ j) (min b t))| := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (stopped_partition_variation_bound A b hA τ hτ t N) (mul_nonneg hK hδ)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_partition_variation_bound
#print axioms Asakura.Chapter3Complete.variation_cross_sum_bound
