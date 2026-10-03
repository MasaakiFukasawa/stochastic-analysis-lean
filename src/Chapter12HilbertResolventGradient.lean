import Chapter12ForcingGradientRiesz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
open scoped Topology ContDiff RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] forcingGradient

theorem hilbert_resolvent_gradient {H E I:Type*} [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T:ℝ) (hT:0≤T) (k:I → C(Icc (0:ℝ) T,H)) (v:I → E)
    (S:C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (a:C(Icc (0:ℝ) T,E))
    (L:E →L[ℝ] E) (A Q:ℝ → E →L[ℝ] E) (hcA:Continuous A) (hcQ:Continuous Q)
    (ell:E →L[ℝ] ℝ) (t:Icc (0:ℝ) T)
    (hd:∀u:H,(fderiv ℝ S a (hilbertKernelForcing k v u)) t=
      hilbertKernelForcing k v u t+L (∫s in 0..t.val,Q s (A s (hilbertKernelForcing k v u (projIcc 0 T hT s))))) :
    forcingGradient S a (hilbertKernelForcing k v) ell t=
      (∑j,ell (v j) • k j t)+∫s in 0..t.val,∑j,ell (L (Q s (A s (v j)))) • k j (projIcc 0 T hT s) := by
  let g := fun s => ∑j,ell (L (Q s (A s (v j)))) • k j (projIcc 0 T hT s)
  have hgc:Continuous g := continuous_finset_sum _ (fun j _ =>
    (ell.continuous.comp (L.continuous.comp (hcQ.clm_apply (hcA.clm_apply continuous_const)))).smul
      ((k j).continuous.comp continuous_projIcc))
  apply ext_inner_right ℝ
  intro u
  rw [forcingGradient_inner,hd,map_add,inner_add_left]
  have h0:ell (hilbertKernelForcing k v u t)=inner ℝ (∑j,ell (v j) • k j t) u := by
    simp only [hilbertKernelForcing_apply,map_sum,map_smul,smul_eq_mul,sum_inner,real_inner_smul_left]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h0]
  congr 1
  let f := fun s => Q s (A s (hilbertKernelForcing k v u (projIcc 0 T hT s)))
  have hfc:Continuous f := hcQ.clm_apply (hcA.clm_apply
    ((hilbertKernelForcing k v u).continuous.comp continuous_projIcc))
  have h1 := (ell.comp L).intervalIntegral_comp_comm (hfc.intervalIntegrable (μ:=volume) 0 t.val)
  have h2 := (innerSL ℝ u).intervalIntegral_comp_comm (hgc.intervalIntegrable (μ:=volume) 0 t.val)
  change (∫s in 0..t.val,ell (L (f s)))=ell (L (∫s in 0..t.val,f s)) at h1
  change (∫s in 0..t.val,inner ℝ u (g s))=inner ℝ u (∫s in 0..t.val,g s) at h2
  change ell (L (∫s in 0..t.val,f s))=inner ℝ (∫s in 0..t.val,g s) u
  rw [←h1]
  apply Eq.trans _ (h2.trans (real_inner_comm _ _))
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [f,g]
  simp only [hilbertKernelForcing_apply,map_sum,map_smul,smul_eq_mul,inner_sum,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm]
  ring
end Asakura.Chapter12
#print axioms Asakura.Chapter12.hilbert_resolvent_gradient
