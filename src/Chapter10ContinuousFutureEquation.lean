import Chapter10FutureWeightedEquation
import Chapter10StateDriftRestriction

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem LinearStateWitness.continuous_future_weighted_equation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X)
    (s t : Icc (0:ℝ) T) (hst : s.val≤t.val) (η : Ω → ℝ)
    (hηm : Measurable[B.F (realTimeClamp s.val)] η) (hη : MemLp η 2 P) (i : Fin d) :
    (∫ w,η w*X w t i ∂P)=(∫ w,η w*X w s i ∂P)+
      ∫ u in s.val..t.val,∫ w,η w*(A u (X w (projIcc 0 T hT u))) i ∂P := by
  letI : MeasurableSpace Ω := m
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hA.continuousOn
  let K : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  let A' := fun u => A (projIcc 0 T hT u).val
  have hAc : Continuous A' := hA.comp (continuous_subtype_val.comp continuous_projIcc)
  have hAK u : ‖A' u‖≤K := (hC _ (projIcc 0 T hT u).property).trans (le_max_left C 0)
  have he u (hu : u∈Icc (0:ℝ) T) : A' u=A u := by
    simp only [A']
    congr 1
    simp [projIcc,hu.1,hu.2]
  have h' := h.congr_drift P B A A' G ξ T hT N X he
  have hh := h'.future_weighted_equation P B A' hAc K hAK G hG ξ hξ2 T hT N X s t hst η hηm hη i
  rw [hh]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hst] at hu
  dsimp only
  rw [he u ⟨s.property.1.trans hu.1,hu.2.trans t.property.2⟩]

end Asakura.Chapter10
