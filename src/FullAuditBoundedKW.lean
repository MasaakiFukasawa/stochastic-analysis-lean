import FullAuditCovarianceIntervals
import FullAuditStieltjesPackage

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable def realTimeClamp {T : EReal} [Fact (0 ≤ T)] (r : ℝ) : ClosedTime T :=
  projIcc 0 T Fact.out (r:EReal)

theorem real_time_clamp_continuous {T : EReal} [Fact (0 ≤ T)] :
    Continuous (realTimeClamp (T := T)) :=
  continuous_projIcc.comp continuous_coe_real_ereal

theorem real_time_clamp_mono {T : EReal} [Fact (0 ≤ T)] :
    Monotone (realTimeClamp (T := T)) := by
  intro s t hst
  exact monotone_projIcc Fact.out (EReal.coe_le_coe hst)

theorem real_time_clamp_eq {T : EReal} [Fact (0 ≤ T)] (r : ℝ) (hr : 0 ≤ r) (hT : (r:EReal) ≤ T) :
    (realTimeClamp (T := T) r : EReal) = r := by
  exact congrArg Subtype.val (projIcc_of_mem (Fact.out : (0:EReal) ≤ T) ⟨by exact_mod_cast hr,hT⟩)

/-- The bounded-martingale case of KW, on every finite real interval at once.
 The returned measures are the Stieltjes measures of the actual QV and signed
 covariance increments, and the inequality is for their total variation.
 Substituting any finite random endpoint is therefore legitimate pathwise. -/
theorem bounded_kw_stieltjes {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : boundedMProcess P F) :
    ∀ᵐ ω ∂P, ∀ b : ℝ, 0 ≤ b → ∃ (α β : Measure ℝ) (ν : SignedMeasure ℝ),
      IsFiniteMeasure α ∧ IsFiniteMeasure β ∧
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ b →
        α.real (Ioc s t) = boundedQV P F hF hle hnull X (realTimeClamp t) ω-
          boundedQV P F hF hle hnull X (realTimeClamp s) ω ∧
        β.real (Ioc s t) = boundedQV P F hF hle hnull Y (realTimeClamp t) ω-
          boundedQV P F hF hle hnull Y (realTimeClamp s) ω ∧
        ν (Ioc s t) = boundedCov P F hF hle hnull X Y (realTimeClamp t) ω-
          boundedCov P F hF hle hnull X Y (realTimeClamp s) ω) ∧
      (∀ f g : ℝ → ℝ, Measurable f → Measurable g →
        (∫⁻ x, ENNReal.ofReal |f x*g x| ∂ν.totalVariation) ≤
          (∫⁻ x, ENNReal.ofReal (f x^2) ∂α)^(1/2:ℝ)*
          (∫⁻ x, ENNReal.ofReal (g x^2) ∂β)^(1/2:ℝ)) := by
  filter_upwards [bounded_cov_interval_cs P F hF hle hnull X Y] with ω hω
  intro b hb
  let A := fun r => boundedQV P F hF hle hnull X (realTimeClamp r) ω
  let B := fun r => boundedQV P F hF hle hnull Y (realTimeClamp r) ω
  let C := fun r => boundedCov P F hF hle hnull X Y (realTimeClamp r) ω
  have hX := boundedQV_properties P F hF hle hnull X
  have hY := boundedQV_properties P F hF hle hnull Y
  have hA : Monotone A := (hX.2.2.1 ω).comp real_time_clamp_mono
  have hB : Monotone B := (hY.2.2.1 ω).comp real_time_clamp_mono
  have hcA : Continuous A := (hX.2.1 ω).comp real_time_clamp_continuous
  have hcB : Continuous B := (hY.2.1 ω).comp real_time_clamp_continuous
  have hcC : Continuous C := by
    exact ((((boundedQV_properties P F hF hle hnull (X+Y)).2.1 ω).sub
      ((boundedQV_properties P F hF hle hnull (X-Y)).2.1 ω)).div_const 4).comp real_time_clamp_continuous
  have hBV : BoundedVariationOn C (Icc 0 b) := by
    obtain ⟨U,V,hU,hV,he⟩ := bounded_cov_in_A P F hF hle hnull X Y ω
    have hv : BoundedVariationOn (fun t => boundedCov P F hF hle hnull X Y t ω) univ := by
      simpa only [he] using increasing_difference_boundedVariation U V hU hV
    apply ne_of_lt
    exact (eVariationOn.comp_le_of_monotoneOn _ _ (real_time_clamp_mono.monotoneOn (Icc 0 b))
      (fun _ _ => mem_univ _)).trans_lt hv.lt_top
  exact stieltjes_interval_package 0 b hb A B C (hA.monotoneOn _) (hB.monotoneOn _)
    (fun x _ => hcA.continuousAt.continuousWithinAt) (fun x _ => hcB.continuousAt.continuousWithinAt)
    hBV (fun x _ => hcC.continuousAt.continuousWithinAt)
    (fun s t _ hst _ => hω _ _ (real_time_clamp_mono hst.le))

end Asakura.FullAudit
