import Chapter12DerivativeGrowthComposition

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1500000

theorem iterated_polynomial_growth_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfB : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k f x‖ ≤ C*(1+‖x‖)^a)
    (hgB : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k g x‖ ≤ C*(1+‖x‖)^a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤ C*(1+‖x‖)^a := by
  obtain ⟨C,hC,a,hfbound⟩ := finite_polynomial_envelope (fun i x => ‖iteratedFDeriv ℝ i f x‖) hfB k
  obtain ⟨D,hD,b,hgbound⟩ := finite_polynomial_envelope (fun i x => ‖iteratedFDeriv ℝ i g x‖) hgB k
  let K := ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*C*D
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  refine ⟨K,Finset.sum_nonneg (fun i _ => by positivity),a+b,fun x => ?_⟩
  apply (norm_iteratedFDeriv_mul_le hf hg x (by simp : (k:ℕ∞ω) ≤ ∞)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), ((k.choose i : ℝ)*C*D)*(1+‖x‖)^(a+b) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      calc
        _ ≤ ((k.choose i : ℝ)*(C*(1+‖x‖)^a))*(D*(1+‖x‖)^b) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hfbound i hik x) (by positivity))
            (hgbound (k-i) (Nat.sub_le _ _) x) (norm_nonneg _) (by positivity)
        _ = _ := by rw [pow_add]; ring
    _ = K*(1+‖x‖)^(a+b) := by rw [Finset.sum_mul]

end Asakura.Chapter12
