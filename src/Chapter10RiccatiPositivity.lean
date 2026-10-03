import Chapter10ContinuousCovarianceIdentification
import Chapter10RiccatiAlgebra

open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- On an interval where a Riccati solution exists, the gain identities turn
it into the actual error covariance. Its nonnegative definiteness is proved. -/
theorem riccati_solution_positive {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n r : ℕ} (B : BrownianSystem P n)
    (F : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hFc : Continuous F)
    (G : Fin d → Fin n → ℝ → ℝ) (hGc : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T)
    (S A Q : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (K : ℝ → Matrix (Fin d) (Fin r) ℝ) (C : ℝ → Matrix (Fin r) (Fin d) ℝ)
    (R : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (hSc : ContinuousOn S (Icc 0 T))
    (hS0 : S 0=(fun i j => ∫ w,ξ w i*ξ w j ∂P))
    (hSd : ∀ t∈Ico 0 T,HasDerivWithinAt S
      (A t*S t+S t*(A t).transpose+Q t-K t*C t*S t) (Ici t) t)
    (hgain : ∀ t∈Ico 0 T,K t*R t=S t*(C t).transpose)
    (hF : ∀ t∈Ico 0 T,(fun i j => (F t (Pi.single j 1)) i)=A t-K t*C t)
    (hGram : ∀ t∈Ico 0 T,(fun i j => ∑ k,G i k t*G j k t)=Q t+K t*R t*(K t).transpose) :
    ∃ (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
      (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)),LinearStateWitness P B F G ξ T hT N X ∧
      ∀ t∈Icc 0 T,(S t).PosSemidef ∧
        S t=(fun i j => ∫ w,X w (projIcc 0 T hT t) i*X w (projIcc 0 T hT t) j ∂P) := by
  letI : MeasurableSpace Ω := m
  apply continuous_covariance_identification P B F hFc G hGc ξ hξ hξ2 T hT S hSc hS0
  intro t ht
  rw [hF t ht,hGram t ht]
  have hid := riccati_covariance_identity (A t) (S t) (Q t) (K t) (C t) (R t) (hgain t ht)
  have he : (A t-K t*C t)*S t+S t*(A t-K t*C t).transpose+
      (Q t+K t*R t*(K t).transpose)=A t*S t+S t*(A t).transpose+Q t-K t*C t*S t := by
    rw [←add_assoc,hid]
  rw [he]
  exact hSd t ht

end Asakura.Chapter10
