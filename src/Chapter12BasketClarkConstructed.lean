import Chapter12ClarkConstructed
import Chapter12BasketPayoffTimeDerivative
import Chapter12ProductTrim
import Chapter12BrownianTerminalStockMoments

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

theorem basket_constructed_clark_integrands {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : StrictMono c)
    (hct : StrictMono (fun n => realTimeClamp (T := ⊤) (c n)))
    (hcut : ∀ n,realTimeClamp (T := ⊤) (c n)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n))
    (hco : ∀ r : ℝ,∃ n,r≤c n)
    (T : ℝ) (hT : 0<T) [Fact (0≤T)]
    (hgen : ∀ U : Lp ℝ 2 (P.trim (B.le (realTimeClamp T))),
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w z => brownianTimeCoordinate P B T z w) inferInstance]
        (U : Ω → ℝ) (P.trim (B.le (realTimeClamp T))))
    (hnat : ∀ (a : Icc (0:ℝ) T) (G : Ω → ℝ),Measurable[B.F (realTimeClamp a.val)] G →
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w (z : BrownianTimeCoordinates d a.val) =>
          brownianTimeCoordinate P B T
            (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans a.property.2⟩) w)
        inferInstance] G (P.trim (B.le (realTimeClamp T))))
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hA : A.det≠0)
    (s wgt : Fin (d+1) → ℝ) (hs : 0<s 0) (hwgt : 0<wgt 0) (K discount : ℝ) :
    let E := progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ))))
    let M2 := fun N => ContinuousM2Witness P B.F N
    let Ito := fun i (H : E) N => ItoCovarianceFormula P B.F (B.W i) H.val N
    let restrict := fun H : E =>
      ((terminal_integrand_restriction P B.F B.mono B.le c hco H T hT.le).2).toLp
        (fun z : Ω × Icc (0:ℝ) T => H.val (z.1,z.2.val))
    let C := fun i w => wgt i*(s i*Real.exp (∑ j,A i j*B.W j (realTimeClamp T) w))
    let V := fun w => ∑ i,C i w
    let Pay := fun w => discount*max (V w-K) 0
    let R := P.trim (B.le (realTimeClamp T))
    letI := probability_trim P _ (B.le (realTimeClamp T))
    letI : MeasurableSpace Ω := B.F (realTimeClamp T)
    ∃ H : Fin (d+1) → E,∃ N : Fin (d+1) → HalfClosedTime → Ω → ℝ,
      (∀ i,M2 (N i)) ∧ (∀ i,Ito i (H i) (N i)) ∧
      Pay =ᵐ[P] (fun w => (∫ z,Pay z ∂R)+∑ i,N i (realTimeClamp T) w) ∧
      (∀ i,Integrable (fun w => (if K<V w then (1:ℝ) else 0)*
        (s i*Real.exp (∑ j,A i j*B.W j (realTimeClamp T) w))) R) ∧
      ∀ j,∀ᵐ t ∂compactTimeMeasure T hT.le,
        (fun w => restrict (H j) (w,t)) =ᵐ[R]
          R[(fun w => discount*(if K<V w then (1:ℝ) else 0)*(∑ i,C i w*A i j))|B.F (realTimeClamp t.val)] := by
  classical
  have hop := brownian_finite_malliavin_operator P B T hT 2 2 (by simp) (by simp) hgen
  have hclark := clark_ocone_actual_finite_integrals P B c hc hcm hct hcut hcc hco T hT hgen
  have hZm := fun j => brownian_time_coordinate_measurable P B T (j,⟨T,hT.le,le_rfl⟩)
  have htransfer : ∀ p : Ω → Prop,(∀ᵐ w ∂P.trim (B.le (realTimeClamp T)),p w) → ∀ᵐ w ∂P,p w :=
    fun p hp => ae_of_ae_trim (B.le (realTimeClamp T)) hp
  let Z := fun j => B.W j (realTimeClamp T)
  let R := P.trim (B.le (realTimeClamp T))
  letI := probability_trim P _ (B.le (realTimeClamp T))
  letI : MeasurableSpace Ω := B.F (realTimeClamp T)
  letI := finite_horizon_L2_nontrivial T hT
  dsimp only at hop ⊢
  obtain ⟨W,hW,D,hclos,hclosed,hcomplete,hgraph,hgraphClosed,hdom,hX⟩ := hop
  obtain ⟨hF,U,hFU,hkernel⟩ := basket_payoff_time_derivative R d ⟨T,hT.le⟩ hT
    W hW D.closure hclosed hgraphClosed Z hZm
      (fun j => hX (j,⟨T,hT.le,le_rfl⟩)) A hA s wgt hs hwgt K discount
  obtain ⟨Y,hY,hDY⟩ := D.closure.mem_graph_iff.mp hFU
  obtain ⟨H,N,hN,hNI,hrep,hconditional⟩ := hclark W hW hX hnat D.closure hgraphClosed Y
  have hraw := hF.coeFn_toLp
  have hrawP : (hF.toLp _ : Ω → ℝ) =ᵐ[P] _ := htransfer _ hraw
  rw [hY] at hrep
  rw [integral_congr_ae hraw] at hrep
  refine ⟨H,N,hN,hNI,hrawP.symm.trans hrep,?_,?_⟩
  · intro i
    have hm : Measurable (fun w => ∑ k,wgt k*(s k*Real.exp (∑ j,A k j*Z j w))) := by
      apply Finset.measurable_sum
      intro k _
      exact ((Real.measurable_exp.comp (Finset.measurable_sum _ (fun j _ => (hZm j).const_mul _))).const_mul _).const_mul _
    exact brownian_terminal_stock_indicator_integrable R d T hT.le W hW Z
      (fun j => hX (j,⟨T,hT.le,le_rfl⟩)) (A i) (s i) _ (measurableSet_lt measurable_const hm)
  · intro j
    have hcond := hconditional j
    rw [hDY] at hcond
    have hk := Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := compactTimeMeasure T hT.le) (ν := R)).quasiMeasurePreserving.ae (hkernel j))
    filter_upwards [hcond,hk] with t ht hkt
    exact ht.trans (condExp_congr_ae (m := B.F (realTimeClamp t.val)) hkt)

end Asakura.Chapter12
