import Chapter10StateRealEquation

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

lemma LinearStateWitness.vector_real_equation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (G : Fin d → Fin n → ℝ → ℝ) (ξ : Ω → Fin d → ℝ)
    (T : ℝ) (hT : 0≤T) (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X) (w : Ω) (t : Icc (0:ℝ) T) :
    X w t=ξ w+(∫ s in 0..t.val,A s (X w (projIcc 0 T hT s)))+
      (fun i => ∑ j,N i j (realTimeClamp t.val) w) := by
  ext i
  have hi : IntervalIntegrable (fun s => A s (X w (projIcc 0 T hT s))) volume 0 t.val :=
    (hA.clm_apply ((X w).continuous.comp continuous_projIcc)).intervalIntegrable 0 t.val
  have hc := (show (Fin d → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj i).intervalIntegral_comp_comm hi
  change (∫ s in 0..t.val,(A s (X w (projIcc 0 T hT s))) i)=(∫ s in 0..t.val,A s (X w (projIcc 0 T hT s))) i at hc
  change X w t i=ξ w i+(∫ s in 0..t.val,A s (X w (projIcc 0 T hT s))) i+∑ j,N i j (realTimeClamp t.val) w
  rw [←hc]
  exact h.real_equation P B A G ξ T hT N X w t i

end Asakura.Chapter10
