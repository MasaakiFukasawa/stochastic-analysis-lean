import EndToEndBrownianJointPast
import FullAuditNaturalFiltration
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace Asakura.EndToEnd

@[instance_reducible] noncomputable def jointPast {Ω ι : Type*} (Z : ι × ℝ≥0 → Ω → ℝ)
    (s : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (q : ι × Iic s) => Z (q.1,q.2.val) ω) inferInstance

theorem jointPast_le {Ω ι : Type*} [MeasurableSpace Ω]
    (Z : ι × ℝ≥0 → Ω → ℝ) (hm : ∀ q, Measurable (Z q)) (s : ℝ≥0) :
    jointPast Z s ≤ (inferInstance : MeasurableSpace Ω) :=
  (Measurable.of_eval (fun q : ι × Iic s => hm (q.1,q.2.val))).comap_le

theorem jointPast_adapted {Ω ι : Type*} (Z : ι × ℝ≥0 → Ω → ℝ)
    (i : ι) (s : ℝ≥0) : Measurable[jointPast Z s] (Z (i,s)) := by
  letI : MeasurableSpace Ω := jointPast Z s
  have h : Measurable[jointPast Z s]
      (fun ω (q : ι × Iic s) => Z (q.1,q.2.val) ω) := Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply (i,(⟨s,show s ≤ s from le_refl s⟩ : Iic s))).comp h

theorem jointPast_mono {Ω ι : Type*} (Z : ι × ℝ≥0 → Ω → ℝ) :
    Monotone (jointPast Z) := by
  intro s t hst
  letI : MeasurableSpace Ω := jointPast Z t
  have h : Measurable[jointPast Z t]
      (fun ω (q : ι × Iic t) => Z (q.1,q.2.val) ω) := Measurable.of_comap_le le_rfl
  exact (Measurable.of_eval (fun q : ι × Iic s =>
    (measurable_pi_apply (q.1,(⟨q.2.val,(show q.2.val ≤ s from q.2.property).trans hst⟩ : Iic t))).comp h)).comap_le

theorem conditional_independent_jointPast {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ι × ℝ≥0 → Ω → ℝ)
    (hm : ∀ q, Measurable (Z q)) (s : ℝ≥0) (U : Ω → ℝ) (hmU : Measurable U)
    (hind : IndepFun U (fun ω (q : ι × Iic s) => Z (q.1,q.2.val) ω) P) :
    P[U | jointPast Z s] =ᵐ[P] fun _ => ∫ ω, U ω ∂P := by
  exact condExp_indep_eq hmU.comap_le (jointPast_le Z hm s)
    (show StronglyMeasurable[MeasurableSpace.comap U inferInstance] U from
      (Measurable.of_comap_le le_rfl).stronglyMeasurable) hind

theorem gaussian_joint_increment_mean {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ι × ℝ≥0 → Ω → ℝ)
    (hZ : IsGaussianProcess Z P) (hmean : ∀ q, ∫ ω, Z q ω ∂P = 0)
    (i : ι) (s t : ℝ≥0) : (∫ ω, Z (i,t) ω - Z (i,s) ω ∂P) = 0 := by
  rw [integral_sub (hZ.hasGaussianLaw_eval (i,t)).integrable
    (hZ.hasGaussianLaw_eval (i,s)).integrable, hmean, hmean, sub_self]

theorem gaussian_joint_martingale {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ι × ℝ≥0 → Ω → ℝ)
    (hZ : IsGaussianProcess Z P) (hm : ∀ q, Measurable (Z q))
    (hmean : ∀ q, ∫ ω, Z q ω ∂P = 0)
    (hcov : ∀ i j u v, cov[Z (i,u), Z (j,v); P] =
      if i = j then ((min u v : ℝ≥0) : ℝ) else 0)
    (i : ι) (s t : ℝ≥0) (hst : s ≤ t) :
    P[Z (i,t) | jointPast Z s] =ᵐ[P] Z (i,s) := by
  have hind := (gaussian_brownian_increment_independent_joint_past P Z hZ hcov s t hst).comp
    (measurable_pi_apply i) measurable_id
  have hD := conditional_independent_jointPast P Z hm s
    (fun ω => Z (i,t) ω-Z (i,s) ω) ((hm _).sub (hm _)) hind
  rw [gaussian_joint_increment_mean P Z hZ hmean] at hD
  have hself : P[Z (i,s) | jointPast Z s] = Z (i,s) :=
    condExp_of_stronglyMeasurable (jointPast_le Z hm s) (jointPast_adapted Z i s).stronglyMeasurable
      (hZ.hasGaussianLaw_eval (i,s)).integrable
  have hsub := condExp_sub (hZ.hasGaussianLaw_eval (i,t)).integrable
    (hZ.hasGaussianLaw_eval (i,s)).integrable (jointPast Z s)
  filter_upwards [hD,hsub] with ω hd hs
  simp only [Pi.sub_apply,hself] at hs
  change P[Z (i,t)-Z (i,s) | jointPast Z s] ω = 0 at hd
  linarith

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.gaussian_joint_martingale
