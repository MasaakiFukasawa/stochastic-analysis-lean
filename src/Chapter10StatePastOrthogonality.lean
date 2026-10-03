import Chapter10FutureWeightedEquation
import Chapter10FutureODEZero
import Chapter10WeightedMeanRegularity

open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Orthogonality at the earlier time propagates forward through the actual
linear SDE. This is the covariance statement used with past innovations. -/
theorem LinearStateWitness.past_orthogonality {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X)
    (s : Icc (0:ℝ) T) (η : Ω → ℝ)
    (hηm : Measurable[B.F (realTimeClamp s.val)] η) (hη : MemLp η 2 P)
    (hzero : ∀ i,(∫ w,η w*X w s i ∂P)=0) :
    ∀ t : Icc (0:ℝ) T,s.val≤t.val → ∀ i,(∫ w,η w*X w t i ∂P)=0 := by
  letI : MeasurableSpace Ω := mΩ
  let m := fun u => ∫ w,η w • X w (projIcc 0 T hT u) ∂P
  obtain ⟨hmc,hmi⟩ := weighted_mean_regular P T hT X h.measurable h.moment η hη
  let L := fun i : Fin d => (show (Fin d → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj i)
  have hcoord u i : m u i=∫ w,η w*X w (projIcc 0 T hT u) i ∂P := by
    have hh := (L i).integral_comp_comm (hmi u)
    simpa only [L,ContinuousLinearMap.proj_apply,Pi.smul_apply,smul_eq_mul,m] using hh.symm
  have hdrift u i : (∫ w,η w*(A u (X w (projIcc 0 T hT u))) i ∂P)=(A u (m u)) i := by
    have hh := ((L i).comp (A u)).integral_comp_comm (hmi u)
    simpa only [ContinuousLinearMap.comp_apply,map_smul,L,ContinuousLinearMap.proj_apply,
      Pi.smul_apply,smul_eq_mul,m] using hh
  have he : ∀ u∈Icc s.val T,∀ i,m u i=∫ v in s.val..u,(A v (m v)) i := by
    intro u hu i
    have hu0 : u∈Icc (0:ℝ) T := ⟨s.property.1.trans hu.1,hu.2⟩
    have hp : projIcc 0 T hT u=⟨u,hu0⟩ := Subtype.ext (by simp [projIcc,hu0.1,hu0.2])
    have hh := h.future_weighted_equation P B A hA K hAK G hG ξ hξ2 T hT N X s ⟨u,hu0⟩ hu.1 η hηm hη i
    rw [hcoord,hp,hh,hzero,zero_add]
    apply intervalIntegral.integral_congr
    intro v _
    exact hdrift v i
  have hz := homogeneous_future_equation_zero m hmc A hA s.val T K s.property.2 (fun u _ => hAK u) he
  intro t hst i
  have hp : projIcc 0 T hT t.val=t := Subtype.ext (by simp [projIcc,t.property.1,t.property.2])
  have hh := congrFun (hz t.val ⟨hst,t.property.2⟩) i
  simpa only [hcoord,hp,Pi.zero_apply] using hh

end Asakura.Chapter10
