import Chapter2LocalCovarianceCS
import Chapter2RealElementaryEnergy
import FullAuditStieltjesPackage

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Every finite real-time interval of an actual local finite-variation
process has bounded variation, directly from its localizers. -/
theorem LocalVariationWitness.finite_boundedVariation
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) {C : ClosedTime T → Ω → ℝ}
    (hC : LocalVariationWitness F C) (ω : Ω) (b : ℝ) (hb : 0 ≤ b) (hbT : (b:EReal) < T) :
    BoundedVariationOn (fun r => C (realTimeClamp r) ω) (Icc 0 b) := by
  obtain ⟨τ,_,_,_,hco,hv⟩ := hC.localizers
  have hbt : realTimeClamp (T := T) b < ⊤ := by
    change (realTimeClamp b : EReal) < T
    rw [real_time_clamp_eq b hb hbT.le]
    exact hbT
  obtain ⟨n,hn⟩ := hco ω _ hbt
  obtain ⟨U,V,hU,hV,he⟩ := hv n ω
  have hUV := increasing_difference_boundedVariation U V hU hV
  have hcomp : BoundedVariationOn (fun r => U (realTimeClamp r)-V (realTimeClamp r)) (Icc 0 b) := by
    apply ne_of_lt
    exact (eVariationOn.comp_le_of_monotoneOn _ _ (real_time_clamp_mono.monotoneOn (Icc 0 b))
      (fun _ _ => mem_univ _)).trans_lt hUV.lt_top
  have heq : EqOn (fun r => C (realTimeClamp r) ω)
      (fun r => U (realTimeClamp r)-V (realTimeClamp r)) (Icc 0 b) := by
    intro r hr
    have hrt : realTimeClamp (T := T) r ≤ τ n ω := (real_time_clamp_mono hr.2).trans hn.le
    simpa only [min_eq_right hrt] using he (realTimeClamp r)
  change eVariationOn (fun r => C (realTimeClamp r) ω) (Icc 0 b) ≠ ∞
  rw [eVariationOn.congr heq]
  exact hcomp

/-- Canonical signed Stieltjes measure of covariance on a finite interval.
The square-root estimate refers to the original quadratic-variation
Stieltjes measures, not to existentially chosen measures. -/
theorem local_covariance_canonical_stieltjes_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y A B C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hA : LocalCovarianceWitness P F X X A) (hB : LocalCovarianceWitness P F Y Y B)
    (hC : LocalCovarianceWitness P F X Y C)
    (b : ℝ) (hb : 0 ≤ b) (hbT : (b:EReal) < T)
    (hAm : ∀ ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 b))
    (hBm : ∀ ω, MonotoneOn (fun r => B (realTimeClamp r) ω) (Icc 0 b))
    (hrA : ∀ ω r, r ∈ Icc 0 b → ContinuousWithinAt (fun s => A (realTimeClamp s) ω) (Icc 0 b ∩ Ici r) r)
    (hrB : ∀ ω r, r ∈ Icc 0 b → ContinuousWithinAt (fun s => B (realTimeClamp s) ω) (Icc 0 b ∩ Ici r) r)
    (hrC : ∀ ω r, r ∈ Icc 0 b → ContinuousWithinAt (fun s => C (realTimeClamp s) ω) (Icc 0 b ∩ Ici r) r) :
    let Cv := fun ω r => C (realTimeClamp r) ω
    let ν := fun ω => bvSigned (Cv ω ∘ intervalClamp 0 b hb)
      (intervalClamp_boundedVariation 0 b hb (Cv ω) (hC.variation.finite_boundedVariation F ω b hb hbT))
      (intervalClamp_right_continuous 0 b hb (Cv ω) (hrC ω)) 0
    ∀ᵐ ω ∂P, ∀ f g : ℝ → ℝ, Measurable f → Measurable g →
      (∫⁻ r, ENNReal.ofReal |f r*g r| ∂(ν ω).totalVariation) ≤
        (∫⁻ r, ENNReal.ofReal (f r^2) ∂(intervalStieltjes 0 b hb (fun r => A (realTimeClamp r) ω) (hAm ω) (hrA ω)).measure)^(1/2:ℝ)*
        (∫⁻ r, ENNReal.ofReal (g r^2) ∂(intervalStieltjes 0 b hb (fun r => B (realTimeClamp r) ω) (hBm ω) (hrB ω)).measure)^(1/2:ℝ) := by
  intro Cv ν
  filter_upwards [local_covariance_interval_cs P F hF hle hnull X Y A B C hX hY hA hB hC] with ω hω
  intro f g hf hg
  let α := (intervalStieltjes 0 b hb (fun r => A (realTimeClamp r) ω) (hAm ω) (hrA ω)).measure
  let β := (intervalStieltjes 0 b hb (fun r => B (realTimeClamp r) ω) (hBm ω) (hrB ω)).measure
  letI : IsFiniteMeasure α := intervalStieltjes_finite _ _ _ _ _ _
  letI : IsFiniteMeasure β := intervalStieltjes_finite _ _ _ _ _ _
  apply stieltjes_integral_real_intervals α β (ν ω) _ f g hf hg
  intro s t hst
  rw [bvSigned_Ioc,intervalStieltjes_Ioc_real,intervalStieltjes_Ioc_real]
  · have hbt : realTimeClamp (T := T) (intervalClamp 0 b hb t) < ⊤ := by
      change (realTimeClamp (intervalClamp 0 b hb t) : EReal) < T
      have hm := intervalClamp_mem 0 b hb t
      rw [real_time_clamp_eq _ hm.1 ((EReal.coe_le_coe hm.2).trans hbT.le)]
      exact (EReal.coe_le_coe hm.2).trans_lt hbT
    exact hω _ _ (real_time_clamp_mono (intervalClamp_mono 0 b hb hst)) hbt
  all_goals exact hst

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.LocalVariationWitness.finite_boundedVariation
#print axioms Asakura.Chapter2Complete.local_covariance_canonical_stieltjes_bound
