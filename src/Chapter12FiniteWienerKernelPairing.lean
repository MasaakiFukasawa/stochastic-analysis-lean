import Chapter12BrownianDerivativeRealization

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem finite_wiener_kernel_pairing {d:ℕ} (T:ℝ) (hT:0≤T)
    (u v:FiniteWienerHilbert d T) (f g:Fin (d+1) → ℝ → ℝ)
    (hf:∀i,(brownianCoordinateProjection T i u:ℝ → ℝ)=ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)] f i)
    (hg:∀i,(brownianCoordinateProjection T i v:ℝ → ℝ)=ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)] g i) :
    inner ℝ u v=∫s in 0..T,∑i,f i s*g i s := by
  let ν := (volume.restrict (Ioi (0:ℝ))).restrict (Iic T)
  have he i:(fun s => inner ℝ (brownianCoordinateProjection T i u s) (brownianCoordinateProjection T i v s))=ᵐ[ν]
      (fun s => f i s*g i s) := by
    filter_upwards [hf i,hg i] with s hs ht
    rw [hs,ht,Real.inner_apply,mul_comm]
  have hi i:Integrable (fun s => f i s*g i s) ν :=
    (L2.integrable_inner (𝕜:=ℝ) (brownianCoordinateProjection T i u) (brownianCoordinateProjection T i v)).congr (he i)
  rw [PiLp.inner_apply]
  change (∑i,inner ℝ (brownianCoordinateProjection T i u) (brownianCoordinateProjection T i v))=_
  have heq i : inner ℝ (brownianCoordinateProjection T i u) (brownianCoordinateProjection T i v)=∫s,f i s*g i s∂ν := by
    rw [L2.inner_def]
    exact integral_congr_ae (he i)
  simp_rw [heq]
  rw [←integral_finsetSum _ (fun i _ => hi i)]
  change (∫s,(∑i,f i s*g i s)∂(volume.restrict (Ioi (0:ℝ))).restrict (Iic T))=_
  rw [Measure.restrict_restrict measurableSet_Iic]
  have hs:Iic T∩Ioi (0:ℝ)=Ioc 0 T := by ext s;simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc];tauto
  rw [hs,intervalIntegral.integral_of_le hT]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.finite_wiener_kernel_pairing
