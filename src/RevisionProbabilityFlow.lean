import Chapter9ProbabilityFlowTransport
import Chapter9ProbabilityFlowDiffeomorphism
import Chapter9ProbabilityFlowUniqueness
import Chapter9Cutoff

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Revision20261101
open Asakura.Chapter9 Asakura.FullAudit

/-- The new theorem 9.3.1: the actual ODE flow transports the density forward,
and its actual inverse transports it backward, for every positive-time strip. -/
theorem probability_flow_marginals {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (R : ℝ) (hR : 0≤R) (hb : ∀ᵐ x ∂μ, ‖x‖≤R)
    (ε T : ℝ) (hε : 0<ε) (hT : ε≤T) :
    ∃ e : EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d),
      Differentiable ℝ e ∧ Differentiable ℝ e.symm ∧
      (volume.withDensity (fun x => ENNReal.ofReal (ouEuclideanDensity μ (ε,x)))).map e =
        volume.withDensity (fun x => ENNReal.ofReal (ouEuclideanDensity μ (T,x))) ∧
      (volume.withDensity (fun x => ENNReal.ofReal (ouEuclideanDensity μ (T,x)))).map e.symm =
        volume.withDensity (fun x => ENNReal.ofReal (ouEuclideanDensity μ (ε,x))) ∧
      ∀ x,∃ X : ℝ → EuclideanSpace ℝ (Fin d), Continuous X ∧ X (T-ε)=e x ∧
        (∀ s∈Icc 0 (T-ε), X s=x+∫ r in 0..s,ouProbabilityVelocity μ d (ε+r) (X r)) ∧
        (∀ s∈Icc 0 (T-ε), X (T-ε-s)=e x+
          ∫ r in 0..s,-ouProbabilityVelocity μ d (T-r) (X (T-ε-r))) := by
  obtain ⟨e,hde,hdi,hm,hflow⟩ := ou_probability_flow_transport μ R hR hb ε (T-ε) hε (sub_nonneg.mpr hT)
  have ht : ε+(T-ε)=T := by ring
  rw [ht] at hm
  refine ⟨e,hde,hdi,hm,homeomorph_inverse_transport e _ _ hm,?_⟩
  intro x
  obtain ⟨X,hXc,hXe,hX⟩ := hflow x
  obtain ⟨K,hFc,hK⟩ := ou_clamped_velocity_regularity μ d R hR hb ε hε
  let b := fun s => ouProbabilityVelocity μ d (ε+max s 0)
  have hX' : ∀ s∈Icc 0 (T-ε), X s=x+∫ r in 0..s,b r (X r) := by
    intro s hs
    rw [hX s hs]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    simp only [b,max_eq_left ((uIcc_of_le hs.1 ▸ hr).1)]
  have hr := integral_path_time_reversal b hFc X hXc x (T-ε) (sub_nonneg.mpr hT) hX'
  refine ⟨X,hXc,hXe,hX,?_⟩
  intro s hs
  rw [hr s hs,hXe]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hrr := (uIcc_of_le hs.1 ▸ hr)
  have hn : 0≤T-ε-r := by linarith [hrr.2,hs.2]
  dsimp [b]
  rw [max_eq_left hn]
  congr 2 <;> ring

/-- The terminal flow's reversed path starts at the chosen terminal point
and reaches its inverse image. No stochastic noise is introduced. -/
theorem reverse_path_endpoints {E : Type*} (e : E ≃ E) (T : ℝ)
    (X : E → ℝ → E) (h0 : ∀ x,X x 0=x) (hT : ∀ x,X x T=e x) (z : E) :
    X (e.symm z) (T-0)=z ∧ X (e.symm z) (T-T)=e.symm z := by
  simp [h0,hT]

/-- Uniqueness on a positive-time strip, from the same bounded-support assumption. -/
theorem probability_flow_uniqueness {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (R : ℝ) (hR : 0≤R) (hb : ∀ᵐ x ∂μ, ‖x‖≤R)
    (ε T : ℝ) (hε : 0<ε) (hT : 0≤T)
    (x : EuclideanSpace ℝ (Fin d))
    (X Y : ℝ → EuclideanSpace ℝ (Fin d)) (hXc : Continuous X) (hYc : Continuous Y)
    (hX : ∀ s∈Icc 0 T,X s=x+∫ r in 0..s,ouProbabilityVelocity μ d (ε+r) (X r))
    (hY : ∀ s∈Icc 0 T,Y s=x+∫ r in 0..s,ouProbabilityVelocity μ d (ε+r) (Y r)) :
    ∀ s∈Icc 0 T,X s=Y s := by
  exact probability_flow_unique μ d R hR hb ε T hε hT x X Y hXc hYc hX hY

/-- Initial-law convergence for the explicit OU Gaussian coupling.
The density/coordinate-law identification is audited separately. -/
theorem probability_flow_cutoff {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x => x) 2 μ) :
    Tendsto (fun t : ℝ => transportDistance (gaussianAffineLaw μ (Real.exp (-t))
      (Real.sqrt (1-Real.exp (-2*t)))) μ) (𝓝 0) (𝓝 0) := by
  have h := (ou_cutoff_tendsto μ hμ).sqrt
  simpa only [Real.sqrt_zero, Real.sqrt_sq_eq_abs,
    transportDistance, abs_of_nonneg (Real.sqrt_nonneg _)] using h

end Asakura.Revision20261101
