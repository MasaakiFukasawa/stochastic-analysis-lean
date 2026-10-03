import Chapter12DerivativeGrowthComposition

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1500000

theorem finite_iterated_polynomial_growth_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (k : ℕ)
    (hfB : ∀ i : ℕ, i ≤ k → ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ i f x‖ ≤ C*(1+‖x‖)^a)
    (hgB : ∀ i : ℕ, i ≤ k → ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ i g x‖ ≤ C*(1+‖x‖)^a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤ C*(1+‖x‖)^a := by
  classical
  have envelope (f : E → ℝ)
      (h : ∀ i : ℕ, i ≤ k → ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
        ‖iteratedFDeriv ℝ i f x‖ ≤ C*(1+‖x‖)^a) :
      ∃ C : ℝ, 1 ≤ C ∧ ∃ a : ℕ, ∀ i, i ≤ k → ∀ x,
        ‖iteratedFDeriv ℝ i f x‖ ≤ C*(1+‖x‖)^a := by
    have h' : ∀i, ∃ C : ℝ, 0≤C ∧ ∃a:ℕ, ∀x:E,
        (if i≤k then ‖iteratedFDeriv ℝ i f x‖ else 0)≤C*(1+‖x‖)^a := by
      intro i
      by_cases hi:i≤k
      · simpa only [if_pos hi] using h i hi
      · exact ⟨0,le_refl _,0,by simp [hi]⟩
    obtain ⟨C,hC,a,ha⟩ := finite_polynomial_envelope _ h' k
    exact ⟨C,hC,a,fun i hi x => by simpa [hi] using ha i hi x⟩
  obtain ⟨C,hC,a,hfbound⟩ := envelope f hfB
  obtain ⟨D,hD,b,hgbound⟩ := envelope g hgB
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

#print axioms Asakura.Chapter12.finite_iterated_polynomial_growth_mul
