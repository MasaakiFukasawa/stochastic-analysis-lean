import Chapter12BrownianFirstVariationKernel
import Chapter12KernelCovarianceLowerBound
import Chapter12ForcingGradientLinear

open MeasureTheory Set
open scoped Topology ContDiff NNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] forcingGradient

theorem brownian_forcing_covariance {n d:ℕ}
    (b:EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))) (hb:ContDiff ℝ ∞ b)
    (hbound:∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T:ℝ) (hT:0≤T)
    (S:C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin (n+1))) → C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin (n+1))))
    (hS:ContDiff ℝ ∞ S)
    (heq:∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT s)))
    (a:C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin (n+1))))
    (v:Fin (d+1) → EuclideanSpace ℝ (Fin (n+1)))
    (K:ℝ≥0) (hK:∀x,‖fderiv ℝ b x‖≤(K:ℝ)) (ell:ℝ) (hell:0≤ell)
    (hv:∀z:EuclideanSpace ℝ (Fin (n+1)),ell*‖z‖^2≤∑j,(inner ℝ z (v j))^2) :
    let U := fun i => forcingGradient S a (hilbertKernelForcing (brownianKernelPath d T) v)
      (PiLp.proj 2 (fun _ : Fin (n+1) => ℝ) i) ⟨T,hT,le_rfl⟩
    ∀z:Fin (n+1) → ℝ,ell*T*Real.exp (-2*(K:ℝ)*T)*(∑i,(z i)^2)≤
      ∑i,z i*((derivativeGram U).mulVec z) i := by
  intro U z
  obtain ⟨J,Q,hcJ,hcQ,hinv,hkern⟩ := brownian_first_variation_kernel b hb hbound T hT S hS heq a d v K hK
  let z' : EuclideanSpace ℝ (Fin (n+1)) := WithLp.toLp 2 z
  have hh := kernel_covariance_lower_bound d T K ell hT K.coe_nonneg hell v hv J Q hcQ hinv z'
    (forcingGradient S a (hilbertKernelForcing (brownianKernelPath d T) v) (innerSL ℝ z') ⟨T,hT,le_rfl⟩)
    (hkern (innerSL ℝ z'))
  rw [euclidean_inner_coordinate_functional,forcingGradient_linear_sum,EuclideanSpace.real_norm_sq_eq] at hh
  rw [derivativeGram_quadratic]
  exact hh
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_forcing_covariance
