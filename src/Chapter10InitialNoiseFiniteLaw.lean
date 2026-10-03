import Chapter10InitialNoiseGaussian
import Mathlib.Topology.Algebra.Module.FiniteDimension

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The initial Gaussian vector together with a finite collection of vector
noise values is jointly Gaussian, using the actual driving integrals. -/
theorem initial_noise_finite_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n k : ℕ} (B : BrownianSystem P n)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j))
    (ξ : Ω → Fin k → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (T : ℝ) (hT : 0≤T) (p : ℕ) (τ : Fin p → Icc (0:ℝ) T) :
    HasGaussianLaw (fun w a => (ξ w,fun i => ∑ j,N i j (realTimeClamp (τ a).val) w)) P := by
  let e : Fin p × Fin d ≃ Fin (p*d) := finProdFinEquiv
  have hg := initial_and_multitime_integrals_gaussian P B
    (fun a => G (e.symm a).2) (fun a j => hG (e.symm a).2 j)
    (fun a => N (e.symm a).2) (fun a j => hN (e.symm a).2 j)
    (fun a j => hNI (e.symm a).2 j) ξ hξ hξg T hT
    (fun a => (τ (e.symm a).1).val) (fun a => (τ (e.symm a).1).property)
  let L : ((Fin k → ℝ) × (Fin (p*d) → ℝ)) →ₗ[ℝ] (Fin p → ((Fin k → ℝ) × (Fin d → ℝ))) :=
    { toFun := fun x a => (x.1,fun i => x.2 (e (a,i)))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hh := hg.map L.toContinuousLinearMap
  change HasGaussianLaw (fun w a => (ξ w,fun i => ∑ j,N (e.symm (e (a,i))).2 j
    (realTimeClamp (τ (e.symm (e (a,i))).1).val) w)) P at hh
  simpa only [Equiv.symm_apply_apply] using hh

end Asakura.Chapter10
