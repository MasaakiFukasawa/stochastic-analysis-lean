import Chapter9VectorIncrement
import Chapter8BrownianForcingPath

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The whole vector of deterministic Ito-integral increments is
independent of the past. Coordinatewise independence alone would not
suffice; the proof uses every linear projection. -/
theorem vector_ito_increment_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d p : ℕ} (B : BrownianSystem P d)
    (G : Fin p → Fin d → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (N : Fin p → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j))
    (R s : ℝ) (hR : 0≤R) (hs : s∈Icc 0 R) :
    Indep (MeasurableSpace.comap
      (fun w i => Finset.sum Finset.univ (fun j : Fin d => N i j (realTimeClamp R) w-N i j (realTimeClamp s) w)) inferInstance)
      (B.F (realTimeClamp s)) P := by
  let Z := fun w i => Finset.sum Finset.univ (fun j : Fin d => N i j (realTimeClamp R) w-N i j (realTimeClamp s) w)
  have hZ : Measurable Z := by
    apply measurable_pi_lambda
    intro i
    exact Finset.measurable_sum _ (fun j _ =>
      (((hN i j).adapted P B.F _ (half_real_time_finite R)).mono (B.le _) le_rfl).sub
        (((hN i j).adapted P B.F _ (half_real_time_finite s)).mono (B.le _) le_rfl))
  let K := fun L : StrongDual ℝ (Fin p → ℝ) => Complex.exp
    (-((∫ r in s..R,∑ j,(∑ i,L (Pi.single i 1)*G i j r)^2 : ℝ):ℂ)/2)
  apply (independence_of_constant_conditional_characteristic P (B.F (realTimeClamp s))
    (B.le _) Z hZ K ?_).2
  intro L
  have hh := vector_ito_increment_characteristic P B G hG N hN hNI
    (fun i => L (Pi.single i 1)) R s hR hs
  have he (w : Ω) : L (Z w)=∑ i,L (Pi.single i 1)*Z w i :=
    dual_coordinate_expansion L (Z w)
  have hfun : (fun w => Complex.exp ((L (Z w):ℂ)*Complex.I))=
      (fun w => Complex.exp ((((∑ i,L (Pi.single i 1)*Z w i):ℝ):ℂ)*Complex.I)) := by
    funext w
    rw [he w]
  rw [hfun]
  exact hh
end Asakura.Chapter9
