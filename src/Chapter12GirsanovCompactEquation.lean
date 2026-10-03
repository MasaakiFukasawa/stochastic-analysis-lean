import Chapter12BrownianCompactCommonLaw
import Chapter6ContinuousCoefficientRegular
import Chapter2CommonTimeEquality

open MeasureTheory Set
open scoped Topology NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter6 Asakura.Chapter2Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem girsanov_compact_equation {Ω:Type*} [MeasurableSpace Ω]
    (P Q:Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {d:ℕ}
    (B:BrownianSystem P d) (BQ:BrownianSystem Q d)
    (L:(Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x:Fin d → ℝ)
    (b:(Fin d → ℝ) → Fin d → ℝ) (hb:Continuous b) (T:ℝ) (hT:0≤T)
    (hW:∀j r,0≤r → BQ.W j (realTimeClamp r)=ᵐ[Q] fun w => B.W j (realTimeClamp r) w-
      ∫s in 0..min T r,stoppedBrownianCoefficient P B
        (fun z:ℝ×(Fin d → ℝ) => L.symm (b (x+L z.2))) T hT j (realTimeClamp s) w) :
    let X := fun w => ContinuousMap.const (Icc (0:ℝ) T) x+L.toContinuousLinearMap.compLeftContinuous ℝ _ (brownianSystemCompactPath B T w)
    let a := fun w => ContinuousMap.const (Icc (0:ℝ) T) x+L.toContinuousLinearMap.compLeftContinuous ℝ _ (brownianSystemCompactPath BQ T w)
    ∀ᵐw∂Q,∀t,X w t=a w t+∫s in 0..t.val,b (X w (projIcc 0 T hT s)) := by
  intro X a
  letI : Nonempty (Icc (0:ℝ) T) := ⟨⟨0,le_rfl,hT⟩⟩
  let Y := brownianSystemCompactPath B T
  let V := brownianSystemCompactPath BQ T
  let Z := fun w s => L.symm (b (X w (projIcc 0 T hT s)))
  have hcZ w:Continuous (Z w) := L.symm.continuous.comp (hb.comp ((X w).continuous.comp continuous_projIcc))
  have hc:Continuous (fun z:ℝ×(Fin d → ℝ) => L.symm (b (x+L z.2))) :=
    L.symm.continuous.comp (hb.comp (continuous_const.add (L.continuous.comp continuous_snd)))
  obtain ⟨_,_,hrep⟩ := stopped_continuous_coefficient_regular P B _ hc T hT
  have hp s (hs:s∈Icc 0 T):projIcc 0 T hT s=⟨s,hs⟩ := Subtype.ext (by simp [projIcc,hs.1,hs.2])
  have he j (t:Icc (0:ℝ) T):(fun w => V w t j)=ᵐ[Q] (fun w => Y w t j-∫s in 0..t.val,Z w s j) := by
    filter_upwards [hW j t.val t.property.1] with w hw
    change BQ.W j (realTimeClamp t.val) w=_
    rw [hw,min_eq_right t.property.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    have hs':s∈Icc 0 T := ⟨hs.1,hs.2.trans t.property.2⟩
    dsimp only
    rw [hrep j w s hs']
    dsimp only [Z]
    rw [hp s hs']
    rfl
  have hall j := continuous_process_common_time_equality Q
    (fun t:Icc (0:ℝ) T => fun w => V w t j)
    (fun t:Icc (0:ℝ) T => fun w => Y w t j-∫s in 0..t.val,Z w s j)
    (fun w => (continuous_apply j).comp (V w).continuous)
    (fun w => ((continuous_apply j).comp (Y w).continuous).sub
      ((intervalIntegral.differentiable_integral_of_continuous ((continuous_apply j).comp (hcZ w))).continuous.comp continuous_subtype_val))
    (he j)
  filter_upwards [ae_all_iff.mpr hall] with w hw
  intro t
  have hev:V w t=Y w t-∫s in 0..t.val,Z w s := by
    funext j
    have hi := (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm
      ((hcZ w).intervalIntegrable (μ:=volume) 0 t.val)
    change (∫s in 0..t.val,Z w s j)=(∫s in 0..t.val,Z w s) j at hi
    change V w t j=Y w t j-(∫s in 0..t.val,Z w s) j
    rw [←hi]
    exact hw j t
  have hint:L (∫s in 0..t.val,Z w s)=∫s in 0..t.val,b (X w (projIcc 0 T hT s)) := by
    have hi := L.toContinuousLinearMap.intervalIntegral_comp_comm ((hcZ w).intervalIntegrable (μ:=volume) 0 t.val)
    change (∫s in 0..t.val,L (Z w s))=L (∫s in 0..t.val,Z w s) at hi
    rw [←hi]
    apply intervalIntegral.integral_congr
    intro s _
    exact L.apply_symm_apply _
  change x+L (Y w t)=(x+L (V w t))+_
  rw [hev,map_sub,hint]
  abel
end Asakura.Chapter12
#print axioms Asakura.Chapter12.girsanov_compact_equation
