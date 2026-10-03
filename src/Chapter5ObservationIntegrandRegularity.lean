import Chapter5ObservationItoIncrement

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Regularity of the actual derivative integrands in the stopped
observation Ito formula, with no covariance assumptions needed. -/
theorem observation_integrand_regularity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    {d k : ℕ} (W : Fin d → ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (index : Fin k → Fin d) (τ : Fin k → ℝ) (b : ℝ) (hb : 0≤b)
    (f : (Fin (k+1) → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (i : Fin (k+1)) :
    let X := fun j t w => W (index j) (min (realTimeClamp (τ j)) t) w
    let K := fun t (_ : Ω) => (finitePrefixTime (T := T) b hb t).val
    let XX : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons K X
    let H := fun z : Ω × ℝ => fderiv ℝ f (fun j => XX j (realTimeClamp z.2) z.1) (Pi.single i 1)
    (∀ w,Measurable (fun r => H (w,r))) ∧
      (∀ r : ℝ,0≤r → (r:EReal)<T → Measurable[F (realTimeClamp r)] (fun w => H (w,r))) ∧
      (∀ R : ℝ,0≤R → (R:EReal)<T → ∀ w,ContinuousOn (fun r => H (w,r)) (Icc 0 R)) := by
  dsimp only
  let X := fun j t w => W (index j) (min (realTimeClamp (τ j)) t) w
  have hstop j : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) (τ j)≤t} := by
    intro t
    by_cases h : realTimeClamp (T := T) (τ j)≤t <;> simp [h]
  have hXs j := (hW (index j)).stopped P F hF hle (fun _ => realTimeClamp (τ j)) (hstop j)
  have hsemi j := local_martingale_semimartingale_decomposition P hT F hF (X j) (hXs j)
  let K := fun t (_ : Ω) => (finitePrefixTime (T := T) b hb t).val
  have hK := clipped_clock_semimartingale P hT F hF b hb
  have hXX j : SemimartingaleDecomposition P F ((Fin.cons K X : Fin (k+1) → ClosedTime T → Ω → ℝ) j)
      ((Fin.cons K (fun _ : Fin k => fun _ : ClosedTime T => fun _ : Ω => (0:ℝ)) : Fin (k+1) → ClosedTime T → Ω → ℝ) j)
      ((Fin.cons (fun _ : ClosedTime T => fun _ : Ω => (0:ℝ)) X : Fin (k+1) → ClosedTime T → Ω → ℝ) j) :=
    by
      cases j using Fin.cases with
      | zero => exact hK
      | succ j => exact hsemi j
  exact multivariate_integrand_regularity P F _ _ _ hXX
    (fun x => fderiv ℝ f x (Pi.single i 1))
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)

end Asakura.Chapter5
