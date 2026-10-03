import Chapter3DiscreteQVMaximal
import Chapter3SummablePathErrors

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The actual square-defect errors converge almost surely uniformly on
[0,b]. This combines the original martingale construction, stopping,
orthogonality, increment-energy estimates, Fatou, Doob and summability.
The remaining deterministic Riemann--Stieltjes error is a separate step. -/
theorem actual_discrete_qv_error_ae_uniform
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Q : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hQ : LocalCovarianceWitness P F X X Q)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτmono : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτtop : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hcofinal : ∀ n ω b, b < ⊤ → ∃ N, b < τ n N ω)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ n j, ∀ᵐ ω ∂P, ∀ t,
      ‖X (min (τ n (j+1) ω) t) ω-X (min (τ n j ω) t) ω‖ ≤ (1/2:ℝ)^n)
    (A : ℕ → ℕ → Ω → ℝ)
    (hA : ∀ n j, Measurable[writtenStoppedSpace m F (τ n j) (hτ n j)] (A n j))
    (hAb : ∀ n j, MemLp (A n j) ∞ P)
    (hAK : ∀ n j, ∀ᵐ ω ∂P, |A n j ω| ≤ K)
    (b : ClosedTime T) (hbT : b < ⊤) (hiQ : Integrable (Q b) P) :
    let E := fun n t ω => ∑' j, A n j ω*partitionDefect X Q (τ n) j (min b t) ω
    ∃ hc : ∀ n ω, Continuous (fun t => E n t ω),
      ∀ᵐ ω ∂P, Tendsto (fun n => continuousPath (E n) (hc n) ω) atTop (𝓝 0) := by
  intro E
  have hh (n) := actual_discrete_qv_maximal_error P F hF hle hnull X Q hX hQ
    (τ n) (hτ n) (hτmono n) (hτtop n) (hτ0 n) (hcofinal n)
    ((1/2:ℝ)^n) K (pow_nonneg (by norm_num) n) hK (hb n) (A n) (hA n) (hAb n) (hAK n) b hbT hiQ
  choose hc hm hn using hh
  refine ⟨hc,?_⟩
  apply ae_zero_of_dyadic_l2_errors P (fun n => continuousPath (E n) (hc n)) hm
    (4*K*Real.sqrt (∫ ω, Q b ω ∂P))
  intro n
  apply (hn n).trans_eq
  congr 1
  ring

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.actual_discrete_qv_error_ae_uniform
