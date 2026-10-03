import Chapter2PathMaximum

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The weak square maximal estimate used in the first Lenglart bound,
derived from the manuscript's continuous-time Doob inequality. -/
theorem continuous_m2_square_maximal
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : ContinuousM2Witness P F X)
    (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | ε ≤ ‖continuousPath X hX.path ω‖} ≤
      (ε ^ 2)⁻¹ * ∫ ω, X ⊤ ω ^ 2 ∂P := by
  have hsqi : Integrable (fun ω => X ⊤ ω ^ 2) P :=
    (memLp_two_iff_integrable_sq (hX.moment ⊤).aestronglyMeasurable).1 (hX.moment ⊤)
  have hconvex : ConvexOn ℝ univ (fun x : ℝ => x ^ 2) := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using norm_rpow_convex 2 (by norm_num)
  have hdom (t) : (fun ω => X t ω ^ 2) ≤ᵐ[P] P[(fun ω => X ⊤ ω ^ 2)|F t] := by
    have hj := conditional_jensen_written (hle t) hconvex
      ((hX.moment ⊤).integrable (by norm_num)) hsqi
    filter_upwards [hj,hX.martingale t ⊤ le_top] with ω hj he
    simpa only [Function.comp_def,he] using hj
  have h := continuous_doob_weak_written P (Fact.out : 0 ≤ T) F hF hle
    (fun t ω => X t ω ^ 2) (fun t => (hX.adapted t).pow_const 2)
    (fun ω t => ((hX.path ω).pow 2).continuousAt.continuousWithinAt) hsqi
    (fun t => .of_forall fun ω => sq_nonneg _) hdom (ε ^ 2) (sq_pos_of_pos hε)
  have he : {ω | ENNReal.ofReal (ε ^ 2) ≤ ⨆ t, ENNReal.ofReal (X t ω ^ 2)} =
      {ω | ε ≤ ‖continuousPath X hX.path ω‖} := by
    ext ω
    have hs := continuous_path_square_sup (continuousPath X hX.path ω)
    change (⨆ t, ENNReal.ofReal (X t ω ^ 2)) = ENNReal.ofReal (‖continuousPath X hX.path ω‖ ^ 2) at hs
    simp only [mem_setOf_eq,hs,ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)]
    exact sq_le_sq₀ hε.le (norm_nonneg _)
  have htop : (⟨T,Fact.out,le_rfl⟩ : ClosedTime T) = ⊤ := by apply Subtype.ext; rfl
  rw [he] at h
  simp only [htop] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hsqi (.of_forall fun ω => sq_nonneg _)) (inv_nonneg.2 (sq_nonneg _)))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_m2_square_maximal
