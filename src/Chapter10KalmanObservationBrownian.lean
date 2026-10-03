import Chapter10KalmanInnovationBrownian
import Chapter10KalmanInnovationIdentification
import Chapter10ActualInnovationBrownian
import Chapter10InnovationNoiseClock

open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Substitute the manuscript's actual Kalman gain and observation inverse
into the identification of any actual error/innovation solution. -/
theorem kalman_observation_innovation_brownian {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d q r : ℕ} (B : BrownianSystem P (q+r))
    (A S : ℝ → Matrix (Fin d) (Fin d) ℝ) (G : ℝ → Matrix (Fin d) (Fin q) ℝ)
    (C : ℝ → Matrix (Fin r) (Fin d) ℝ) (D J : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (hA : Continuous A) (hS : Continuous S) (hG : Continuous G)
    (hC : Continuous C) (hD : Continuous D) (hJ : Continuous J)
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (hξ0 : ∫ w,ξ w ∂P=0) (T : ℝ) (hT : 0<T) [Fact (0≤(T:EReal))]
    (hinit : S 0=(fun i j => ∫ w,ξ w i*ξ w j ∂P))
    (hJD : ∀ t∈Ico 0 T,J t*D t=1) (hDJ : ∀ t∈Ico 0 T,D t*J t=1)
    (hSym : ∀ t∈Ico 0 T,(S t).transpose=S t)
    (hSd : ∀ t∈Ico 0 T,HasDerivWithinAt S
      (A t*S t+S t*(A t).transpose+G t*(G t).transpose-S t*((C t).transpose*((J t).transpose*J t)*C t)*S t) (Ici t) t) :
    let K := fun t => S t*(C t).transpose*((J t).transpose*J t)
    let F := fun t => A t-K t*C t
    let U := fun t => matrixOperatorMap (finiteBlocks (F t) 0 (J t*C t) (0 : Matrix (Fin r) (Fin r) ℝ))
    let E := fun i j t => finiteBlocks (G t) (-(K t*D t)) (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ) i j
    ∀ N X,LinearStateWitness P B U E (fun w => extendZero (r := r) (ξ w)) T hT.le N X →
      ∀ R s : ℝ,0≤R → R<T → s∈Icc 0 R → ∀ (Y : Ω → C(Icc (0:ℝ) s,Fin r → ℝ)),
        Asakura.Chapter9.nullAugmentedInformation (m := m) P (MeasurableSpace.comap Y inferInstance)=
          Asakura.Chapter9.nullAugmentedInformation (m := m) P
            (pathInformation T X tailIndex (projIcc 0 T hT.le s)) → ∀ v : Fin r → ℝ,
        P[(fun w => Complex.exp (((∑ i,v i*(X w (projIcc 0 T hT.le R) (tailIndex i)-
          X w (projIcc 0 T hT.le s) (tailIndex i))):ℝ)*Complex.I))|
          Asakura.Chapter9.nullAugmentedInformation (m := m) P
            (MeasurableSpace.comap Y inferInstance)]=ᵐ[P]
          fun _ => Complex.exp (-((R-s:ℝ):ℂ)*((∑ i,(v i)^2:ℝ):ℂ)/2) := by
  intro K F U E N X h R s hR hRT hs Y hinfo v
  rw [hinfo]
  exact kalman_innovation_brownian P B A S G C D J hA hS hG hC hD hJ
    ξ hξ hξg hξ0 T hT hinit hJD hDJ hSym hSd N X h R s hR hRT hs v

end Asakura.Chapter10
