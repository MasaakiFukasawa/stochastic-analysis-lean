import Chapter12AsianNaturalOperator
import Chapter12ClarkFiniteIntegrals
import Chapter12AsianHedgeCoefficient
import Chapter12ProductTrim

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

theorem asian_natural_clark_holdings {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hpaths : ∀ w,Continuous (fun t => B t w))
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : StrictMono c)
    (hct : StrictMono (fun n => realTimeClamp (T := ⊤) (c n)))
    (hcut : ∀ n,realTimeClamp (T := ⊤) (c n)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n))
    (hco : ∀ r : ℝ,∃ n,r≤c n)
    (T : ℝ≥0) (hT : 0<T) [Fact (0≤(T:ℝ))]
    (x σ r K : ℝ) (hx : 0<x) (hσ : 0<σ) :
    let BS := naturalBrownianSystem P B hB hm hpaths
    let X := brownianCompactPath B hpaths T
    let E := progressiveEnergyIntegrands BS.F c (P.prod (volume.restrict (Ioi (0:ℝ))))
    let M2 := fun N => ContinuousM2Witness P BS.F N
    let Ito := fun (H : E) N => ItoCovarianceFormula P BS.F (BS.W 0) H.val N
    let restrict := fun H : E =>
      ((terminal_integrand_restriction P BS.F BS.mono BS.le c hco H T T.property).2).toLp
        (fun z : Ω × Icc (0:ℝ) T => H.val (z.1,z.2.val))
    let R := P.trim (BS.le (realTimeClamp T))
    let Pay := fun w => Real.exp (-r*T)*max (asianPathAverage x r T T.property σ (X w)-K) 0
    letI := probability_trim P _ (BS.le (realTimeClamp T))
    letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
    ∃ H : E,∃ N : HalfClosedTime → Ω → ℝ,
      M2 N ∧ Ito H N ∧
      Pay =ᵐ[P] (fun w => (∫ z,Pay z ∂R)+N (realTimeClamp T) w) ∧
      ∀ᵐ t ∂compactTimeMeasure T T.property,∀ᵐ w ∂R,
        restrict H (w,t)/(σ*Real.exp (-r*t.val)*stockPathValue x σ r T (X w) t)=
          Real.exp (-r*(T-t.val))/(T*stockPathValue x σ r T (X w) t)*
            R[(fun v => (if K<asianPathAverage x r T T.property σ (X v) then (1:ℝ) else 0)*
              asianRemainingMoment T T.property x σ r 0 (X v) t)|BS.F (realTimeClamp t.val)] w := by
  let BS := naturalBrownianSystem P B hB hm hpaths
  let X := brownianCompactPath B hpaths T
  have hop := asian_natural_malliavin_operator P B hB hm hpaths T hT x σ r K hx hσ
  have hclark := clark_ocone_actual_finite_integrals P BS c hc hcm hct hcut hcc hco
    T (show (0:ℝ)<T from hT) (natural_brownian_Lp_information P B hB hm hpaths T T.property 2)
  have hnat := natural_brownian_past_information P B hB hm hpaths T
  have hid := trim_identity_preserving P (BS.F (realTimeClamp T)) (BS.le _)
  have htransfer : ∀ p : Ω → Prop,(∀ᵐ w ∂P.trim (BS.le (realTimeClamp T)),p w) → ∀ᵐ w ∂P,p w :=
    fun p hp => ae_of_ae_trim (BS.le (realTimeClamp T)) hp
  let R := P.trim (BS.le (realTimeClamp T))
  letI := probability_trim P _ (BS.le (realTimeClamp T))
  letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
  letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
  dsimp only at hop ⊢
  obtain ⟨W,hW,D,hclosed,hgraph,hX,hF,U,hFU,hkernel⟩ := hop
  obtain ⟨Y,hY,hDY⟩ := D.mem_graph_iff.mp hFU
  obtain ⟨H,N,hN,hNI,hrep,hconditional⟩ := hclark W hW hX hnat D hgraph Y
  have hraw := hF.coeFn_toLp
  have hrawP : (hF.toLp _ : Ω → ℝ) =ᵐ[P] _ := htransfer _ hraw
  rw [hY] at hrep
  have hmean := integral_congr_ae hraw
  rw [hmean] at hrep
  refine ⟨H 0,N 0,hN 0,hNI 0,?_,?_⟩
  · have hh := hrawP.symm.trans hrep
    filter_upwards [hh] with w hw
    have hsum : (∑ i : Fin (0+1),N i (realTimeClamp T) w)=N 0 (realTimeClamp T) w :=
      Fin.sum_univ_one _
    rwa [hsum] at hw
  · have hcond := hconditional 0
    rw [hDY] at hcond
    exact asian_clark_holdings_coefficient R T (show (0:ℝ)<T from hT)
      (fun t => BS.F (realTimeClamp t.val)) X x σ r K hx hσ _ _ hcond hkernel

end Asakura.Chapter12
