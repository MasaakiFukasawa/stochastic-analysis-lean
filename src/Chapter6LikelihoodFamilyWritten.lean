import Chapter6LikelihoodBasisConstruction
import Chapter6LinearLikelihoodDensity

open MeasureTheory Set Filter Finset Matrix
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false
local instance (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))

/-- The likelihood family is obtained from constructed Ito integrals,
not from an assumed score or an assumed measurable likelihood. -/
theorem likelihood_family_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ)
    (b : Fin n → ℝ × (Fin d → ℝ) → Fin d → ℝ) (hb : ∀ k,Continuous (b k))
    (R : ℝ) (hR : 0<R) (K : ℝ) (hK : 0≤K) (hbb : ∀ k z,‖WithLp.toLp 2 (b k z)‖≤K) :
    let X := brownianObservedPath P B L x R hR.le
    let info := fun w k l => ∫ r in 0..R,∑ j,b k (r,fun i => B.W i (realTimeClamp r) w) j*
      b l (r,fun i => B.W i (realTimeClamp r) w) j
    ∃ N : Fin n → Fin d → HalfClosedTime → Ω → ℝ,
      (∀ k j,LocalMProcessWitness P B.F (N k j)) ∧
      (∀ k j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => stoppedBrownianCoefficient P B (b k) R hR.le j (realTimeClamp z.2) z.1) (N k j)) ∧
      (let score := fun w k => ∑ j,N k j (realTimeClamp R) w
       ∃ (a : C(Icc (0:ℝ) R,Fin d → ℝ) → Fin n → ℝ)
         (J : C(Icc (0:ℝ) R,Fin d → ℝ) → Matrix (Fin n) (Fin n) ℝ),
         Measurable a ∧ Measurable J ∧ score=ᵐ[P] a ∘ X ∧ info=J ∘ X ∧
         (∀ θ,Integrable (fun w => Real.exp (quadraticLogLikelihood (info w) (score w) θ)) P ∧
           (∫ w,Real.exp (quadraticLogLikelihood (info w) (score w) θ) ∂P)=1 ∧
           IsProbabilityMeasure (P.withDensity (fun w => ENNReal.ofReal (Real.exp (quadraticLogLikelihood (info w) (score w) θ))))) ∧
         (∀ θ,(P.withDensity (fun w => ENNReal.ofReal (Real.exp (quadraticLogLikelihood (info w) (score w) θ)))).map X=
           (P.map X).withDensity (fun y => ENNReal.ofReal (Real.exp (quadraticLogLikelihood (J y) (a y) θ)))) ∧
         (∀ y,(J y).PosDef → (∀ θ,quadraticLogLikelihood (J y) (a y) θ≤quadraticLogLikelihood (J y) (a y) ((J y)⁻¹ *ᵥ a y)) ∧
           (∀ θ,quadraticLogLikelihood (J y) (a y) θ=quadraticLogLikelihood (J y) (a y) ((J y)⁻¹ *ᵥ a y) ↔ θ=(J y)⁻¹ *ᵥ a y))) := by
  let X := brownianObservedPath P B L x R hR.le
  let H := fun k => stoppedBrownianCoefficient P B (b k) R hR.le
  let info := fun w k l => ∫ r in 0..R,∑ j,b k (r,fun i => B.W i (realTimeClamp r) w) j*
      b l (r,fun i => B.W i (realTimeClamp r) w) j
  obtain ⟨N,hN,hNI⟩ := likelihood_basis_constructed P B b hb R hR.le K hK hbb
  let score := fun w k => ∑ j,N k j (realTimeClamp R) w
  obtain ⟨a,J,ham,hJm,ha,hJ⟩ := likelihood_path_data P B L x b hb R hR K hK hbb N hN hNI
  have hreg k := stopped_brownian_coefficient_regular P B (b k) (hb k) R hR.le K (hbb k)
  have hinfo : (fun w k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w)=info := by
    funext w k l
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc 0 R := by simpa [uIcc_of_le hR.le] using hr
    exact sum_congr rfl (fun j _ => congrArg₂ (· * ·) ((hreg k).2.2.2 j w r hr') ((hreg l).2.2.2 j w r hr'))
  have hd θ := linear_likelihood_density P B H N (fun k => (hreg k).1) (fun k => (hreg k).2.1) hN hNI K hK
    (fun k j t w => (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => H k i t w)) j).trans ((hreg k).2.2.1 t w)) R hR.le θ
  have hfamily := common_likelihood_family P X (brownian_observed_path_measurable P B L x R hR.le)
    info score J a hJm ham (ae_of_all _ (fun w => congrFun hJ w)) ha
  refine ⟨N,hN,hNI,a,J,ham,hJm,ha,hJ,?_,hfamily.2.2.1,?_⟩
  · intro θ
    have hw w := congrFun hinfo w
    simpa only [hw] using hd θ
  · intro y hy
    exact quadratic_likelihood_unique_maximum (J y) hy (a y)

end Asakura.Chapter6
