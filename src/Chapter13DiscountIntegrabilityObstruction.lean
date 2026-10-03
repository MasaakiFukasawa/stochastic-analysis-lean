import Mathlib.Probability.Distributions.Geometric
import Chapter13Numeraire

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable def halfGeometric : Measure ℕ := geometricMeasure ⟨1/2,by constructor <;> norm_num⟩
instance : IsProbabilityMeasure halfGeometric := by unfold halfGeometric;infer_instance

theorem positive_nonintegrable_growth :
    (∀n:ℕ,1≤(2:ℝ)^n) ∧ ¬Integrable (fun n:ℕ => (2:ℝ)^n) halfGeometric := by
  refine ⟨fun n => one_le_pow₀ (by norm_num),?_⟩
  intro hi
  have hs := (integrable_geometricMeasure_iff (p:=⟨1/2,by constructor <;> norm_num⟩) (by intro h;have hh:=congrArg Subtype.val h;norm_num at hh)).mp hi
  have he:∀n:ℕ,(1-(1/2:ℝ))^n*(1/2)*‖(2:ℝ)^n‖=1/2 := by
    intro n
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (by norm_num) n)]
    norm_num
    rw [mul_assoc, mul_left_comm,←mul_pow]
    norm_num
  simp_rw [he] at hs
  have ht:=hs.tendsto_atTop_zero
  have heq:=tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at heq

theorem inverse_growth_integrable : Integrable (fun n:ℕ => ((2:ℝ)^n)⁻¹) halfGeometric := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  filter_upwards [] with n
  rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) n))]
  exact inv_le_one_of_one_le₀ (positive_nonintegrable_growth.1 n)

theorem conditional_growth_not_identity :
    halfGeometric[(fun n:ℕ => (2:ℝ)^n)|⊤] ≠ (fun n:ℕ => (2:ℝ)^n) := by
  rw [condExp_of_not_integrable positive_nonintegrable_growth.2]
  intro he
  have hh := congrFun he 0
  norm_num at hh
end Asakura.Chapter13
#print axioms Asakura.Chapter13.positive_nonintegrable_growth
#print axioms Asakura.Chapter13.conditional_growth_not_identity
