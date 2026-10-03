import Chapter4FinitePathLift
import Chapter3ProductFormula
import Chapter3LocalItoFormula
import Chapter2ContinuousIntegrand

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma local_product_integrals_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X Y C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hY : LocalMProcessWitness P F Y) (hC : LocalCovarianceWitness P F X Y C) :
    ∃ I J : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F I ∧ LocalMProcessWitness P F J ∧
      ItoCovarianceFormula P F X (fun z => Y (realTimeClamp z.2) z.1) I ∧
      ItoCovarianceFormula P F Y (fun z => X (realTimeClamp z.2) z.1) J ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → X t w*Y t w=X ⊥ w*Y ⊥ w+I t w+J t w+C t w) := by
  have hreg (Z : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z) :
      (∀ r : ℝ,0≤r → (r:EReal)<T → Measurable[F (realTimeClamp r)] (Z (realTimeClamp r))) ∧
      (∀ b : ℝ,0≤b → (b:EReal)<T → ∀ w,ContinuousOn (fun r => Z (realTimeClamp r) w) (Icc 0 b)) := by
    refine ⟨fun r hr hrT => hZ.adapted P F _ (real_time_below r hr hrT),?_⟩
    intro b hb hbT w r hr
    exact ((hZ.path P F w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hbT))).comp
      real_time_clamp_continuous.continuousAt).continuousWithinAt
  obtain ⟨I,hI,hIi⟩ := continuous_adapted_ito_exists P hT F hF hle hnull X hX (fun z => Y (realTimeClamp z.2) z.1) (hreg Y hY).1 (hreg Y hY).2
  obtain ⟨J,hJ,hJi⟩ := continuous_adapted_ito_exists P hT F hF hle hnull Y hY (fun z => X (realTimeClamp z.2) z.1) (hreg X hX).1 (hreg X hX).2
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  refine ⟨I,J,hI,hJ,hIi,hJi,?_⟩
  exact semimartingale_product_formula P hT F hF hle hnull X Y (fun _ _ => 0) (fun _ _ => 0) X Y C I J
    (local_martingale_semimartingale_decomposition P hT F hF X hX)
    (local_martingale_semimartingale_decomposition P hT F hF Y hY) hC c (fun k => (hc k).le) hcT hcc
    (local_ito_as_semimartingale_integral P hT F hF X I _ hI hIi c (fun k => (hc k).le))
    (local_ito_as_semimartingale_integral P hT F hF Y J _ hJ hJi c (fun k => (hc k).le))

lemma local_product_integral_formula {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X Y C I J : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hY : LocalMProcessWitness P F Y) (hC : LocalCovarianceWitness P F X Y C)
    (hI : LocalMProcessWitness P F I) (hJ : LocalMProcessWitness P F J)
    (hIi : ItoCovarianceFormula P F X (fun z => Y (realTimeClamp z.2) z.1) I)
    (hJi : ItoCovarianceFormula P F Y (fun z => X (realTimeClamp z.2) z.1) J) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → X t w*Y t w=I t w+J t w+C t w := by
  obtain ⟨I',J',hI',hJ',hIi',hJi',hp⟩ := local_product_integrals_constructed P hT F hF hle hnull X Y C hX hY hC
  have heI := ItoCovarianceFormula.unique P hT F hF hle hnull X I' I _ hX hI' hI hIi' hIi
  have heJ := ItoCovarianceFormula.unique P hT F hF hle hnull Y J' J _ hY hJ' hJ hJi' hJi
  filter_upwards [hp,heI,heJ,hX.initial P F] with w hw hi hj hx
  intro t ht
  simpa only [hi t ht,hj t ht,hx,Pi.zero_apply,zero_mul,zero_add] using hw t ht

end Asakura.Chapter7
