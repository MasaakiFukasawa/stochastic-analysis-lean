import Chapter12ForcedVariationalStability

open Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Constructing the Hilbert- or Banach-valued first-variation equation
requires only continuous forcing, including the Brownian interpolation kernel. -/
theorem forced_variational_exists_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (hcA : Continuous A) (K : ℝ≥0)
    (hA : ∀ s,‖A s‖≤(K:ℝ)) (R : ℝ → E) (hcR : Continuous R)
    (T C : ℝ) (hT : 0≤T) (hC : 0≤C)
    (hR : ∀ s,s∈Icc 0 T → ‖R s‖≤C) :
    ∃ X : ℝ → E,Continuous X ∧
      (∀ s,s∈Icc 0 T → X s=R s+∫ t in 0..s,A t (X t)) ∧
      ∀ s,s∈Icc 0 T → ‖X s‖≤Real.exp (((K:ℝ)+1)*T)*C := by
  have hLip (t : ℝ) : LipschitzWith K (A t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm,← map_sub]
    exact ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA t) (norm_nonneg _))
  obtain ⟨X,hcX,hX⟩ := Asakura.Chapter8.forced_integral_equation_exists T hT K
    (fun t x => A t x) ((hcA.comp continuous_fst).clm_apply continuous_snd) hLip R hcR
  refine ⟨X,hcX,hX,?_⟩
  have he := forced_variational_path_stability A A R 0 X 0 hcA hcA hcX continuous_const
    T ((K:ℝ)+1) 0 C 0 hT (by positivity) le_rfl hC le_rfl
    (fun s _ => (hA s).trans (by linarith))
    (fun s _ => by simp) (fun s hs => by simpa using hR s hs)
    (fun s _ => by simp) hX (fun s _ => by simp)
  intro s hs
  simpa only [Pi.zero_apply,sub_zero,mul_zero,add_zero] using he s hs

end Asakura.Chapter12
