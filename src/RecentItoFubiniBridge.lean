import RecentItoFubiniCheck
import FullAuditMartingaleHilbert
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped Topology ENNReal
namespace Asakura.RecentItoFubini
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written

/-- The final step of the newly printed isometry proof, with the exact
stopped identity, dominated square limit, and monotone bracket limit explicit.
It does NOT claim to construct the stopping times or prove the Doob bound. -/
theorem stopped_isometry_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (Qn : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (bound : Ω → ℝ)
    (hXm : ∀ n, AEStronglyMeasurable (fun ω => Xn n ω ^ 2) P)
    (hbound : Integrable bound P)
    (hdom : ∀ n, ∀ᵐ ω ∂P, ‖Xn n ω ^ 2‖ ≤ bound ω)
    (hXlim : ∀ᵐ ω ∂P, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω)))
    (hQi : ∀ n, Integrable (Qn n) P) (hQ : Integrable Q P)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun n => Qn n ω))
    (hQlim : ∀ᵐ ω ∂P, Tendsto (fun n => Qn n ω) atTop (𝓝 (Q ω)))
    (stopped : ∀ n, (∫ ω, Xn n ω ^ 2 ∂P) = ∫ ω, Qn n ω ∂P) :
    (∫ ω, X ω ^ 2 ∂P) = ∫ ω, Q ω ∂P := by
  have hx : Tendsto (fun n => ∫ ω, Xn n ω ^ 2 ∂P) atTop
      (𝓝 (∫ ω, X ω ^ 2 ∂P)) := by
    apply tendsto_integral_of_dominated_convergence bound hXm hbound hdom
    exact hXlim.mono (fun ω h => h.pow 2)
  have hq := integral_tendsto_of_tendsto_of_monotone hQi hQ hmono hQlim
  simp only [stopped] at hx
  exact tendsto_nhds_unique hx hq

/-- Concrete instantiation: the integral of an integrable family of actual
continuous L2 martingales has an actual continuous martingale process witness.
Completeness is supplied by the previous manuscript formalization, not by a
new unproved CompleteSpace hypothesis. The complete-filtration hypothesis
below is retained from that earlier formalization. -/
theorem m2_bochner_process_exists {Ω E : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (μ : Measure E) (Z : E → continuousM2Terminal P F) (hZ : Integrable Z μ) :
    ∃ X, ContinuousM2Witness P F X ∧
      X ⊤ =ᵐ[P] ((∫ x, (Z x : Lp ℝ 2 P) ∂μ) : Lp ℝ 2 P) := by
  letI : CompleteSpace (continuousM2Terminal P F) :=
    continuous_m2_hilbert_complete P F hF hle hnull
  let N : continuousM2Terminal P F := ∫ x, Z x ∂μ
  obtain ⟨X, hX, hterm⟩ := N.property
  refine ⟨X, hX, ?_⟩
  have hi := (continuousM2Terminal P F).subtypeL.integral_comp_comm hZ
  have he : (N : Lp ℝ 2 P) = ∫ x, (Z x : Lp ℝ 2 P) ∂μ := hi.symm
  rw [← he]
  exact hterm
end Asakura.RecentItoFubini
#print axioms Asakura.RecentItoFubini.stopped_isometry_limit
#print axioms Asakura.RecentItoFubini.m2_bochner_process_exists
#print axioms Asakura.FullAudit.continuous_m2_hilbert_complete
