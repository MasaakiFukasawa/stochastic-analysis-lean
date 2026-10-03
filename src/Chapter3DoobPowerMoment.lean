import Chapter3DoobSquareMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The strong Doob bound in pth-moment form; finiteness is only used to convert to real integrals. -/
theorem continuous_m2_path_power_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : ContinuousM2Witness P F X)
    (p : ℝ) (hp : 1 < p)
    (hSi : Integrable (fun ω => ‖continuousPath X hX.path ω‖^p) P)
    (hXi : Integrable (fun ω => |X ⊤ ω|^p) P) :
    (∫ ω, ‖continuousPath X hX.path ω‖^p ∂P) ≤
      (p/(p-1))^p*(∫ ω, |X ⊤ ω|^p ∂P) := by
  have hp0 : 0 < p := by linarith
  have hC : 0 ≤ p/(p-1) := by positivity
  have hi := (hX.moment ⊤).integrable (by norm_num)
  have habs t : Measurable[F t] (fun ω => |X t ω|) := by
    letI : MeasurableSpace Ω := F t
    simpa only [Real.norm_eq_abs] using (hX.adapted t).norm
  have hd t : (fun ω => |X t ω|) ≤ᵐ[P] P[(fun ω => |X ⊤ ω|)|F t] := by
    have hj := conditional_jensen_written (hle t) abs_convex_written hi hi.abs
    filter_upwards [hj,hX.martingale t ⊤ le_top] with ω hj he
    simpa only [Function.comp_def,he] using hj
  have h := continuous_doob_strong_written P (Fact.out : 0 ≤ T) F hF hle (fun t ω => |X t ω|) habs
    (fun ω t => (hX.path ω).abs.continuousAt.continuousWithinAt) hi.abs
    (fun _ => Filter.Eventually.of_forall (fun ω => abs_nonneg _)) hd p hp
  have htop : (⟨T,Fact.out,le_rfl⟩ : ClosedTime T) = ⊤ := by apply Subtype.ext; rfl
  have hen ω : (⨆ t, ENNReal.ofReal |X t ω|) = ENNReal.ofReal ‖continuousPath X hX.path ω‖ := by
    rw [ofReal_norm,ContinuousMap.enorm_eq_iSup_enorm]
    simp only [continuousPath,ContinuousMap.coe_mk,← ofReal_norm,Real.norm_eq_abs]
  simp only [htop,hen] at h
  have eS ω : ENNReal.ofReal ‖continuousPath X hX.path ω‖ ^ p =
      ENNReal.ofReal (‖continuousPath X hX.path ω‖^p) :=
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le
  have eX ω : ENNReal.ofReal |X ⊤ ω| ^ p = ENNReal.ofReal (|X ⊤ ω|^p) :=
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le
  simp only [eS,eX] at h
  rw [← ofReal_integral_eq_lintegral_ofReal hSi
      (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (norm_nonneg _) p)),
    ← ofReal_integral_eq_lintegral_ofReal hXi
      (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (abs_nonneg _) p))] at h
  have hpow := ENNReal.rpow_le_rpow h hp0.le
  rw [← ENNReal.rpow_mul,ENNReal.mul_rpow_of_nonneg _ _ hp0.le,← ENNReal.rpow_mul] at hpow
  have he : (1/p)*p = 1 := by field_simp
  simp only [he,ENNReal.rpow_one,ENNReal.ofReal_rpow_of_nonneg hC hp0.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hC p)] at hpow
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg hC p)
    (integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) p)))).mp hpow

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.continuous_m2_path_power_moment
