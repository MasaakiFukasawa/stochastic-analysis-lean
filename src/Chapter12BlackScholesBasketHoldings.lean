import Chapter12BasketClarkConstructed
import Chapter12BasketHoldingsCoefficient

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

theorem basket_black_scholes_clark_holdings {Ω : Type*} [MeasurableSpace Ω]
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
    (x wgt : Fin (d+1) → ℝ) (hx : ∀ i,0<x i) (hwgt : 0<wgt 0) (r K : ℝ) :
    let Stock := fun i (t : ℝ) w => x i*Real.exp ((r-(∑ j,(A i j)^2)/2)*t+∑ j,A i j*B.W j (realTimeClamp t) w)
    let E := progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ))))
    let M2 := fun N => ContinuousM2Witness P B.F N
    let Ito := fun i (H : E) N => ItoCovarianceFormula P B.F (B.W i) H.val N
    let restrict := fun H : E =>
      ((terminal_integrand_restriction P B.F B.mono B.le c hco H T hT.le).2).toLp
        (fun z : Ω × Icc (0:ℝ) T => H.val (z.1,z.2.val))
    let V := fun w => ∑ i,wgt i*Stock i T w
    let Pay := fun w => Real.exp (-r*T)*max (V w-K) 0
    let R := P.trim (B.le (realTimeClamp T))
    letI := probability_trim P _ (B.le (realTimeClamp T))
    letI : MeasurableSpace Ω := B.F (realTimeClamp T)
    let Holding := fun i (t : Icc (0:ℝ) T) w => Real.exp (-r*(T-t.val))*wgt i/Stock i t.val w*
      R[(fun v => (if K<V v then (1:ℝ) else 0)*Stock i T v)|B.F (realTimeClamp t.val)] w
    ∃ H : Fin (d+1) → E,∃ N : Fin (d+1) → HalfClosedTime → Ω → ℝ,
      (∀ i,M2 (N i)) ∧ (∀ i,Ito i (H i) (N i)) ∧
      Pay =ᵐ[P] (fun w => (∫ z,Pay z ∂R)+∑ i,N i (realTimeClamp T) w) ∧
      ∀ᵐ t ∂compactTimeMeasure T hT.le,∀ᵐ w ∂R,∀ j,
        (∑ i,A i j*((Real.exp (-r*t.val)*Stock i t.val w)*Holding i t w))=restrict (H j) (w,t) := by
  let Stock := fun i (t : ℝ) w => x i*Real.exp ((r-(∑ j,(A i j)^2)/2)*t+∑ j,A i j*B.W j (realTimeClamp t) w)
  let s := fun i => x i*Real.exp ((r-(∑ j,(A i j)^2)/2)*T)
  have hs : 0<s 0 := mul_pos (hx 0) (Real.exp_pos _)
  have hmain := basket_constructed_clark_integrands P B c hc hcm hct hcut hcc hco T hT hgen hnat
    A hA s wgt hs hwgt K (Real.exp (-r*T))
  have hstock (i : Fin (d+1)) (w : Ω) :
      s i*Real.exp (∑ j,A i j*B.W j (realTimeClamp T) w)=Stock i T w := by
    dsimp only [s,Stock]
    rw [Real.exp_add]
    ring
  let R := P.trim (B.le (realTimeClamp T))
  letI := probability_trim P _ (B.le (realTimeClamp T))
  letI : MeasurableSpace Ω := B.F (realTimeClamp T)
  dsimp only at hmain ⊢
  simp_rw [hstock] at hmain
  obtain ⟨H,N,hN,hNI,hrep,hX,hcond⟩ := hmain
  refine ⟨H,N,hN,hNI,hrep,?_⟩
  filter_upwards [ae_all_iff.mpr hcond] with t ht
  apply basket_clark_holdings_coefficient R (B.F (realTimeClamp t.val)) A r T t.val wgt
    (fun i w => Stock i t.val w) (fun i w => (mul_pos (hx i) (Real.exp_pos _)).ne')
    (fun i w => (if K<(∑ k,wgt k*Stock k T w) then (1:ℝ) else 0)*Stock i T w) hX
  intro j
  apply (ht j).trans
  apply condExp_congr_ae
  apply ae_of_all
  intro w
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Asakura.Chapter12
