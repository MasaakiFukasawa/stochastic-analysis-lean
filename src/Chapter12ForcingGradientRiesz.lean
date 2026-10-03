import Chapter12CylinderGradientDirection
import Chapter12HilbertKernelFactorization
import Chapter12ScalarForcingPath
import Chapter12GaussianJetCylinder
import Mathlib.Analysis.InnerProductSpace.Dual

open MeasureTheory Set
open scoped ContDiff RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

noncomputable def forcingGradient {H E K:Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace K] [CompactSpace K]
    (S:C(K,E) → C(K,E)) (a:C(K,E)) (R:H →L[ℝ] C(K,E)) (ell:E →L[ℝ] ℝ) (t:K) : H :=
  (InnerProductSpace.toDual ℝ H).symm
    ((ell.comp (ContinuousMap.evalCLM ℝ t)).comp ((fderiv ℝ S a).comp R))

theorem forcingGradient_inner {H E K:Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace K] [CompactSpace K]
    (S:C(K,E) → C(K,E)) (a:C(K,E)) (R:H →L[ℝ] C(K,E)) (ell:E →L[ℝ] ℝ) (t:K) (u:H) :
    inner ℝ (forcingGradient S a R ell t) u=ell ((fderiv ℝ S a (R u)) t) :=
  InnerProductSpace.toDual_symm_apply

theorem gaussian_forcing_gradient {Ω H E K:Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace K] [CompactSpace K]
    (P:Measure Ω) (W:H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S:C(K,E) → C(K,E)) (hS:ContDiff ℝ ∞ S) (a:C(K,E))
    {N:ℕ} (e:Fin N → H) (L:(Fin N → ℝ) →L[ℝ] C(K,E))
    (R:H →L[ℝ] C(K,E)) (hR:R=L.comp (hilbertCoordinates e)) (ell:E →L[ℝ] ℝ) (t:K)
    (f:GaussianJet N) (hf:f.f=fun z => ell (S (a+L z) t)) (w:Ω) :
    (f.toCylinder e).gradient P W w=
      forcingGradient S (a+L (fun j => W (e j) w)) R ell t := by
  apply ext_inner_right ℝ
  intro u
  rw [cylinder_gradient_direction,forcingGradient_inner]
  change fderiv ℝ f.f (fun j => W (e j) w) (hilbertCoordinates e u)=_
  rw [hf]
  let z := fun j => W (e j) w
  have hd := ((ell.comp (ContinuousMap.evalCLM ℝ t)).hasFDerivAt).comp z
    (((hS.differentiable (by simp)) (a+L z)).hasFDerivAt.comp z
      ((hasFDerivAt_const a z).add L.hasFDerivAt))
  simp only [zero_add] at hd
  change HasFDerivAt (fun z => ell (S (a+L z) t))
    ((ell.comp (ContinuousMap.evalCLM ℝ t)).comp ((fderiv ℝ S (a+L z)).comp L)) z at hd
  rw [hd.fderiv,hR]
  rfl
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussian_forcing_gradient
