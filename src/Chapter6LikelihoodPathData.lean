import Chapter6CoefficientPathFactor
import Chapter6InformationPathFactor
import Chapter6CommonLikelihoodFamily

open MeasureTheory Set Filter Finset Matrix
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
local instance (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))

/-- Build the finite score and information path functions from the actual
Ito integrals and coefficient time integrals, with one common exceptional set. -/
theorem likelihood_path_data {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ)
    (b : Fin n → ℝ × (Fin d → ℝ) → Fin d → ℝ) (hb : ∀ k,Continuous (b k))
    (R : ℝ) (hR : 0<R) (K : ℝ) (hK : 0≤K) (hbb : ∀ k z,‖WithLp.toLp 2 (b k z)‖≤K)
    (N : Fin n → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ k j,LocalMProcessWitness P B.F (N k j))
    (hNI : ∀ k j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => stoppedBrownianCoefficient P B (b k) R hR.le j (realTimeClamp z.2) z.1) (N k j)) :
    let X := brownianObservedPath P B L x R hR.le
    let score := fun w k => ∑ j,N k j (realTimeClamp R) w
    let info := fun w k l => ∫ r in 0..R,∑ j,b k (r,fun i => B.W i (realTimeClamp r) w) j*
      b l (r,fun i => B.W i (realTimeClamp r) w) j
    ∃ (a : C(Icc (0:ℝ) R,Fin d → ℝ) → Fin n → ℝ)
      (J : C(Icc (0:ℝ) R,Fin d → ℝ) → Matrix (Fin n) (Fin n) ℝ),
      Measurable a ∧ Measurable J ∧ score=ᵐ[P] a ∘ X ∧ info=J ∘ X := by
  let X := brownianObservedPath P B L x R hR.le
  have hex k j := brownian_coefficient_ito_path_factor P B L x (b k) (hb k) R hR K hK (hbb k) j (N k j) (hN k j) (hNI k j)
  choose f hfm hfe using hex
  have hiex k l := information_entry_path_factor P B L x (b k) (b l) (hb k) (hb l) R hR.le
  choose J hJm hJe using hiex
  refine ⟨fun y k => ∑ j,f k j y,fun y k l => J k l y,?_,?_,?_,?_⟩
  · exact measurable_pi_iff.mpr (fun k => Finset.measurable_sum _ (fun j _ => hfm k j))
  · exact measurable_pi_iff.mpr (fun k => measurable_pi_iff.mpr (fun l => hJm k l))
  · filter_upwards [ae_all_iff.2 (fun k => ae_all_iff.2 (hfe k))] with w hw
    funext k
    exact sum_congr rfl (fun j _ => hw k j)
  · funext w k l
    exact congrFun (hJe k l) w

end Asakura.Chapter6
