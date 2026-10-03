import Chapter3MomentHolder

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.Chapter3Complete
set_option maxHeartbeats 1200000

/-- The time-integral power estimate used repeatedly in the moment proof,
including exponent one. Integrability of the unpowered function is derived. -/
theorem integral_power_holder
    {D : Type*} [MeasurableSpace D] (μ : Measure D) [IsFiniteMeasure μ]
    (f : D → ℝ) (hf : ∀ x,0≤f x) (q : ℝ) (hq : 1≤q)
    (hi : Integrable (fun x => f x^q) μ) :
    Integrable f μ ∧ (∫ x,f x ∂μ)^q≤μ.real univ^(q-1)*(∫ x,f x^q ∂μ) := by
  by_cases hq1 : q=1
  · subst q
    simpa using And.intro hi (le_refl (∫ x,f x ∂μ))
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have ha : 0<1/q := one_div_pos.mpr hq0
  have ha1 : 1/q<1 := (div_lt_one hq0).2 (lt_of_le_of_ne hq (Ne.symm hq1))
  obtain ⟨hj,hb⟩ := fractional_moment_holder μ (fun x => f x^q) (fun _ => 1) hi (integrable_const 1)
    (fun x => Real.rpow_nonneg (hf x) q) (fun _ => zero_le_one) (1/q) ha ha1
  have he x : (f x^q)^(1/q)*(1:ℝ)^(1-1/q)=f x := by
    rw [Real.one_rpow,mul_one,← Real.rpow_mul (hf x)]
    simp [hq0.ne']
  simp_rw [he] at hj hb
  simp only [integral_const,smul_eq_mul,mul_one] at hb
  have hp := Real.rpow_le_rpow (integral_nonneg hf) hb hq0.le
  have hE : 0≤∫ x,f x^q ∂μ := integral_nonneg (fun x => Real.rpow_nonneg (hf x) q)
  rw [Real.mul_rpow (Real.rpow_nonneg hE _) (Real.rpow_nonneg (measureReal_nonneg) _),
    ← Real.rpow_mul hE,← Real.rpow_mul (measureReal_nonneg)] at hp
  have haeq : (1/q)*q=1 := by field_simp
  have hbeq : (1-1/q)*q=q-1 := by field_simp <;> ring
  rw [haeq,hbeq,Real.rpow_one,mul_comm] at hp
  exact ⟨hj,hp⟩

end Asakura.Chapter4
