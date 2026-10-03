import Chapter10LinearPathUniqueness

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter10
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The pathwise solution of a linear equation depends continuously and
linearly on the initial value and the additive forcing path. -/
theorem linear_solution_operator_exists {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K)
    (T : ℝ) (hT : 0≤T) :
    ∃ S : (E × C(Icc (0:ℝ) T,E)) →L[ℝ] C(Icc (0:ℝ) T,E),
      ∀ p t,S p t=p.1+(∫ s in 0..t.val,A s (S p (projIcc 0 T hT s)))+p.2 t := by
  have hb s : LipschitzWith K (A s) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hAK s) (norm_nonneg _))
  have hc : Continuous (Function.uncurry fun s x => A s x) := (hA.comp continuous_fst).clm_apply continuous_snd
  obtain ⟨S,hSc,hS⟩ := time_dependent_additive_path_map_exists (fun s x => A s x) K hc hb T hT
  have hi p t : IntervalIntegrable (fun s => A s (S p (projIcc 0 T hT s))) volume 0 t :=
    (hA.clm_apply ((S p).continuous.comp continuous_projIcc)).intervalIntegrable 0 t
  have hadd p q : S (p+q)=S p+S q := by
    apply linear_forced_paths_unique A hA K hAK T hT (p+q) _ _ (hS (p+q))
    intro t
    simp only [ContinuousMap.add_apply,map_add,Prod.fst_add,Prod.snd_add]
    rw [intervalIntegral.integral_add (hi p t.val) (hi q t.val),hS p t,hS q t]
    abel
  have hsmul (c : ℝ) p : S (c • p)=c • S p := by
    apply linear_forced_paths_unique A hA K hAK T hT (c • p) _ _ (hS (c • p))
    intro t
    simp only [ContinuousMap.smul_apply,map_smul,Prod.smul_fst,Prod.smul_snd]
    rw [intervalIntegral.integral_smul,hS p t]
    simp only [smul_add]
  let L : (E × C(Icc (0:ℝ) T,E)) →ₗ[ℝ] C(Icc (0:ℝ) T,E) :=
    { toFun := S,map_add' := hadd,map_smul' := hsmul }
  exact ⟨⟨L,hSc⟩,hS⟩

end Asakura.Chapter10
