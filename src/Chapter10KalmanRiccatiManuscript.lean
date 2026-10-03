import Chapter10KalmanRiccatiExistence
import Chapter10ObservationInverse

open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Finite-horizon Riccati existence under the printed continuity and
invertibility assumptions, with the actual inverse of D D-transpose. -/
theorem kalman_riccati_manuscript {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d q r : ℕ} (B : BrownianSystem P (q+r))
    (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (G : ℝ → Matrix (Fin d) (Fin q) ℝ)
    (C : ℝ → Matrix (Fin r) (Fin d) ℝ) (D : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (T : ℝ) (hT : 0≤T)
    (hA : ContinuousOn A (Icc 0 T)) (hG : ContinuousOn G (Icc 0 T))
    (hC : ContinuousOn C (Icc 0 T)) (hD : ContinuousOn D (Icc 0 T))
    (hdet : ∀ t∈Icc 0 T,(D t).det≠0)
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P) :
    ∃ S : ℝ → Matrix (Fin d) (Fin d) ℝ,Continuous S ∧
      S 0=(fun i j => ∫ w,ξ w i*ξ w j ∂P) ∧
      (∀ t∈Ico 0 T,HasDerivWithinAt S
        (A t*S t+S t*(A t).transpose+G t*(G t).transpose-
          S t*((C t).transpose*((D t*(D t).transpose)⁻¹)*C t)*S t) (Ici t) t) ∧
      ∀ t∈Icc 0 T,(S t).PosSemidef := by
  letI : MeasurableSpace Ω := m
  let p := fun t => (projIcc 0 T hT t).val
  have hpc : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpm t : p t∈Icc (0:ℝ) T := (projIcc 0 T hT t).property
  have hp t (ht : t∈Icc (0:ℝ) T) : p t=t := by simp [p,projIcc,ht.1,ht.2]
  let A' := A ∘ p
  let G' := G ∘ p
  let C' := C ∘ p
  let D' := D ∘ p
  have ha : Continuous A' := hA.comp_continuous hpc hpm
  have hg : Continuous G' := hG.comp_continuous hpc hpm
  have hc : Continuous C' := hC.comp_continuous hpc hpm
  have hd : Continuous D' := hD.comp_continuous hpc hpm
  let J := fun t => (D' t)⁻¹
  have hj : Continuous J := continuous_observation_inverse D' hd (fun t => hdet _ (hpm t))
  have hid t := observation_inverse_identities (D' t) (hdet _ (hpm t))
  obtain ⟨S,hSc,hSzero,hSd,hSp⟩ := kalman_riccati_finite_exists P B A' G' C' D' J ha hg hc hd hj ξ hξ hξ2 T hT
    (fun t _ => (hid t).1) (fun t _ => (hid t).2)
  refine ⟨S,hSc,hSzero,?_,hSp⟩
  intro t ht
  simpa only [A',G',C',D',J,Function.comp_apply,hp t ⟨ht.1,ht.2.le⟩,observation_covariance_inverse] using hSd t ht

end Asakura.Chapter10
