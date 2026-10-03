import Chapter12ConcreteCylinderOperator

open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The polynomial bounds defining the cylinder class are preserved under
linear reparametrization of its finite coordinates. -/
theorem iterated_polynomial_growth_comp_linear {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : F → G) (hf : ContDiff ℝ ∞ f) (L : E →L[ℝ] F)
    (hg : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k f x‖ ≤ C*(1+‖x‖)^a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ C*(1+‖x‖)^a := by
  obtain ⟨C,hC,a,hb⟩ := hg k
  let A := max 1 ‖L‖
  have hA : 0 ≤ A := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
  refine ⟨C*A^a*‖L‖^k,by positivity,a,fun x => ?_⟩
  rw [L.iteratedFDeriv_comp_right hf x (by simp)]
  have hx : 1+‖L x‖ ≤ A*(1+‖x‖) := by
    have h1 : 1 ≤ A := le_max_left _ _
    have h2 : ‖L‖ ≤ A := le_max_right _ _
    nlinarith [L.le_opNorm x,norm_nonneg x]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (L x)‖*(∏ _ : Fin k, ‖L‖) :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ (C*(A*(1+‖x‖))^a)*‖L‖^k := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
      exact (hb _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx a) hC)
    _ = _ := by rw [mul_pow]; ring

/-- Addition of two smooth coordinate functions preserves every growth
bound, including the function itself at derivative order zero. -/
theorem iterated_polynomial_growth_add {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : E → F) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfB : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k f x‖ ≤ C*(1+‖x‖)^a)
    (hgB : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k g x‖ ≤ C*(1+‖x‖)^a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => f y+g y) x‖ ≤ C*(1+‖x‖)^a := by
  obtain ⟨C,hC,a,hb⟩ := hfB k
  obtain ⟨D,hD,b,hd⟩ := hgB k
  refine ⟨C+D,add_nonneg hC hD,max a b,fun x => ?_⟩
  have hx : 1 ≤ 1+‖x‖ := by linarith [norm_nonneg x]
  change ‖iteratedFDeriv ℝ k (f+g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f x‖+‖iteratedFDeriv ℝ k g x‖ := norm_add_le _ _
    _ ≤ C*(1+‖x‖)^a+D*(1+‖x‖)^b := add_le_add (hb x) (hd x)
    _ ≤ C*(1+‖x‖)^(max a b)+D*(1+‖x‖)^(max a b) :=
      add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (le_max_left _ _)) hC)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (le_max_right _ _)) hD)
    _ = _ := by ring

end Asakura.Chapter12
