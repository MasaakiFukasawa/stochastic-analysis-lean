import Chapter3BDGTwo

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Hölder in moment form, with integrability derived for the fractional powers. -/
theorem fractional_moment_holder
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U V : Ω → ℝ) (hU : Integrable U P) (hV : Integrable V P)
    (hUp : ∀ ω, 0 ≤ U ω) (hVp : ∀ ω, 0 ≤ V ω)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    Integrable (fun ω => U ω^a*V ω^(1-a)) P ∧
    (∫ ω, U ω^a*V ω^(1-a) ∂P) ≤ (∫ ω, U ω ∂P)^a*(∫ ω, V ω ∂P)^(1-a) := by
  have hb : 0 < 1-a := by linarith
  have hpow (W : Ω → ℝ) (hW : Integrable W P) (hWp : ∀ ω, 0 ≤ W ω)
      (r : ℝ) (hr : 0 < r) : MemLp (fun ω => W ω^r) (ENNReal.ofReal (1/r)) P := by
    have hm : AEStronglyMeasurable (fun ω => W ω^r) P :=
      ((Real.continuous_rpow_const hr.le).comp_aestronglyMeasurable hW.aestronglyMeasurable)
    apply (integrable_norm_rpow_iff hm (by simpa using hr) (by simp)).mp
    have he : (fun ω => ‖W ω^r‖^(ENNReal.ofReal (1/r)).toReal) = W := by
      funext ω
      rw [ENNReal.toReal_ofReal (by positivity),Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (hWp ω) r),← Real.rpow_mul (hWp ω)]
      simp [hr.ne']
    rw [he]
    exact hW
  have hU' := hpow U hU hUp a ha
  have hV' := hpow V hV hVp (1-a) hb
  have hc : (1/a).HolderConjugate (1/(1-a)) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact (lt_div_iff₀ ha).mpr (by linarith)
    · simp
  letI := hc.ennrealOfReal
  have hi := hU'.integrable_mul hV'
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hc
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (hUp ω) a))
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (hVp ω) (1-a))) hU' hV'
  have heU : (fun ω => (U ω^a)^(1/a)) = U := by
    funext ω
    rw [← Real.rpow_mul (hUp ω)]
    simp [ha.ne']
  have heV : (fun ω => (V ω^(1-a))^(1/(1-a))) = V := by
    funext ω
    rw [← Real.rpow_mul (hVp ω)]
    simp [hb.ne']
  rw [heU,heV] at hh
  have heprod : ((fun ω => U ω^a) * (fun ω => V ω^(1-a))) =
      (fun ω => U ω^a*V ω^(1-a)) := by funext ω; rfl
  rw [heprod] at hi
  exact ⟨hi, by simpa using hh⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.fractional_moment_holder
