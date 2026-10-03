import Chapter9ProbabilityContinuityEquation
import Chapter9FlowDensityTransport
import Chapter9ProbabilityFlowC1

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The constructed probability-flow ODE transports the actual OU density
at epsilon to its actual density at epsilon+T. -/
theorem ou_probability_flow_transport {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (R : ℝ) (hR : 0≤R) (hb : ∀ᵐ x ∂μ,‖x‖≤R)
    (ε T : ℝ) (hε : 0<ε) (hT : 0≤T) :
    ∃ e : EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d),
      Differentiable ℝ e ∧ Differentiable ℝ e.symm ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
        (fun x => ENNReal.ofReal (ouEuclideanDensity μ (ε,x)))).map e=
        volume.withDensity (fun x => ENNReal.ofReal (ouEuclideanDensity μ (ε+T,x))) ∧
      ∀ x,∃ X : ℝ → EuclideanSpace ℝ (Fin d),Continuous X ∧ X T=e x ∧
        ∀ s∈Icc 0 T,X s=x+∫ r in 0..s,ouProbabilityVelocity μ d (ε+r) (X r) := by
  let F := fun s => ouProbabilityVelocity μ d (ε+max s 0)
  let D := fun s y => fderiv ℝ (F s) y
  let P := fun z : ℝ × EuclideanSpace ℝ (Fin d) => ouEuclideanDensity μ (ε+max z.1 0,z.2)
  have ht (s : ℝ) : 0<ε+max s 0 := by linarith [le_max_right s (0:ℝ)]
  obtain ⟨K,hFc,hK⟩ := ou_clamped_velocity_regularity μ d R hR hb ε hε
  obtain ⟨hFd,hDc⟩ := ou_clamped_velocity_c1 μ d R hb ε hε
  have hPc : Continuous P := (ou_euclidean_density_smooth μ).continuousOn.comp_continuous
    (by fun_prop : Continuous (fun z : ℝ × EuclideanSpace ℝ (Fin d) => (ε+max z.1 0,z.2)))
    (fun z => ht z.1)
  have hd (s : ℝ) (hs : 0<s) (x : EuclideanSpace ℝ (Fin d)) :
      HasFDerivAt P (fderiv ℝ (ouEuclideanDensity μ) (ε+s,x)) (s,x) := by
    have hpd := ((ou_euclidean_density_smooth μ).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds
        (show 0<(ε+s,x).1 by linarith))).differentiableAt (by simp)
    have hφ : HasFDerivAt (fun z : ℝ × EuclideanSpace ℝ (Fin d) => (ε+z.1,z.2))
        (ContinuousLinearMap.id ℝ _) (s,x) := by
      simpa only [Prod.add_def,zero_add,id_eq] using! (hasFDerivAt_id (s,x)).const_add (ε,0)
    have hh := hpd.hasFDerivAt.comp (s,x) hφ
    have hh' : HasFDerivAt (fun z : ℝ × EuclideanSpace ℝ (Fin d) =>
        ouEuclideanDensity μ (ε+z.1,z.2))
        (fderiv ℝ (ouEuclideanDensity μ) (ε+s,x)) (s,x) := by
      simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using! hh
    apply hh'.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hs] with z hz
    dsimp [P]
    rw [max_eq_left hz.le]
  have hpde s (hs : s∈Ioo 0 T) x :
      (fderiv ℝ P (s,x)) (1,F s x)=
        -P (s,x)*(operatorMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (D s x)).trace := by
    rw [(hd s hs.1 x).fderiv]
    dsimp only [F,D,P]
    rw [max_eq_left hs.1.le]
    exact ou_probability_continuity_equation μ R hb (ε+s) (by linarith [hs.1]) x
  obtain ⟨e,hde,hdi,hm,hflow⟩ := classical_flow_density_transport
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis volume F D hFc hDc
    (fun s x => (hFd s x).hasFDerivAt) K hK T hT P hPc (fderiv ℝ P)
    (fun s hs x => (hd s hs.1 x).differentiableAt.hasFDerivAt) hpde
  refine ⟨e,hde,hdi,?_,?_⟩
  · simpa only [P,max_self,add_zero,max_eq_left hT] using hm
  · intro x
    obtain ⟨X,hcX,hXT,hX⟩ := hflow x
    refine ⟨X,hcX,hXT,?_⟩
    intro s hs
    rw [hX s hs]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp [F]
    rw [max_eq_left ((uIcc_of_le hs.1 ▸ hr).1)]
end Asakura.Chapter9
