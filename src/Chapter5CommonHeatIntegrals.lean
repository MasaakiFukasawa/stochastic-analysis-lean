import Chapter5ObservationContinuousRegularity
import Chapter5BackwardHeatGradient
import Chapter2ContinuousIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Construct a single family of Ito integrals from the Gaussian gradient
up to and including the final observation time. It does not depend on
which earlier cutoff was used to apply the C² Ito formula. -/
theorem common_heat_gradient_integrals
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {d k : ℕ} (W : Fin d → ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (index : Fin k → Fin d) (τ : Fin k → ℝ) (S : ℝ) (hS : 0≤S)
    (ν : Measure (Fin k → ℝ)) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : Fin k → ℝ => z) ν)
    (f : (Fin k → ℝ) → ℝ) (D : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hDc : Continuous D)
    (C : ℝ≥0) (hD : ∀ x,‖D x‖≤C) :
    let X : Fin k → ClosedTime T → Ω → ℝ := fun j t w => W (index j) (min (realTimeClamp (τ j)) t) w
    let H : Fin k → Ω × ℝ → ℝ := fun i (z : Ω × ℝ) =>
      ∫ y,D ((fun j => X j (realTimeClamp z.2) z.1)+
        Real.sqrt (S-(finitePrefixTime (T := T) S hS (realTimeClamp z.2)).val) • y) (Pi.single i 1) ∂ν
    (∀ i z,|H i z|≤C) ∧ (∀ i w,Measurable (fun r => H i (w,r))) ∧
      ∃ J : Fin k → ClosedTime T → Ω → ℝ,
        (∀ i,LocalMProcessWitness P F (J i)) ∧
        (∀ i,ItoCovarianceFormula P F (W (index i)) (H i) (J i)) := by
  classical
  dsimp only
  obtain ⟨_,hmean,hmeanB,_⟩ := averaged_bounded_gradient ν hi f D hd hDc C hD
  let ψ := fun i (x : Fin (k+1) → ℝ) => ∫ y,D ((fun j => x j.succ)+Real.sqrt (S-x 0) • y) (Pi.single i 1) ∂ν
  have hDi (x : Fin (k+1) → ℝ) : Integrable (fun y => D ((fun j => x j.succ)+Real.sqrt (S-x 0) • y)) ν :=
    Integrable.of_bound (hDc.comp (by fun_prop)).aestronglyMeasurable C (ae_of_all _ fun _ => hD _)
  have he i x : ψ i x=(∫ y,D ((fun j => x j.succ)+Real.sqrt (S-x 0) • y) ∂ν) (Pi.single i 1) :=
    (ContinuousLinearMap.integral_apply (hDi x) (Pi.single i 1)).symm
  have hψ i : Continuous (ψ i) := by
    have hh := (hmean.comp (show Continuous (fun x : Fin (k+1) → ℝ => ((fun j => x j.succ),S-x 0)) by fun_prop)).clm_apply
      (continuous_const (y := (Pi.single i 1 : Fin k → ℝ)))
    exact hh.congr (fun x => (he i x).symm)
  have hψB i x : |ψ i x|≤C := by
    rw [he]
    change ‖(∫ y,D ((fun j => x j.succ)+Real.sqrt (S-x 0) • y) ∂ν) (Pi.single i 1)‖≤C
    calc
      _ ≤ ‖∫ y,D ((fun j => x j.succ)+Real.sqrt (S-x 0) • y) ∂ν‖*‖(Pi.single i 1 : Fin k → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C := by simpa [Pi.norm_single] using hmeanB (fun j => x j.succ) (S-x 0)
  let X : Fin k → ClosedTime T → Ω → ℝ := fun j t w => W (index j) (min (realTimeClamp (τ j)) t) w
  let clock := fun t (_ : Ω) => (finitePrefixTime (T := T) S hS t).val
  let XX : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons clock X
  let H : Fin k → Ω × ℝ → ℝ := fun i (z : Ω × ℝ) => ψ i (fun j => XX j (realTimeClamp z.2) z.1)
  have hreg i := observation_continuous_function_regularity P hT F hF hle W hW index τ S hS (ψ i) (hψ i)
  have hJ i := continuous_adapted_ito_exists P hT F hF hle hnull (W (index i)) (hW (index i)) (H i)
    (hreg i).2.1 (hreg i).2.2
  choose J hJM hJI using hJ
  exact ⟨(fun i z => hψB i (fun j => XX j (realTimeClamp z.2) z.1)),(fun i => (hreg i).1),J,hJM,hJI⟩

end Asakura.Chapter5
