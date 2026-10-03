import Chapter12BasketSelfFinancing
import Chapter12BlackScholesBasketHoldings
import Chapter12VectorNaturalInformation
import Chapter12BasketRestrictedHoldings

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology BigOperators
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

noncomputable def BasketReplication {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hA : A.det≠0)
    (x : Fin (d+1) → ℝ) (r : ℝ)
    (φ : Fin (d+1) → progressiveEnergyIntegrands B.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ)))))
    (N : Fin (d+1) → HalfClosedTime → Ω → ℝ) : Prop :=
    let σ := fun i => Real.sqrt (∑ j,A i j^2)
    let W := fun i => brownianUnitDirection P B (fun j => A i j/σ i)
      (volatility_row_normalization A hA i).2.2.1
    ∃ ψ : Fin (d+1) → progressiveEnergyIntegrands B.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ)))),
    ∃ M : Fin (d+1) → HalfClosedTime → Ω → ℝ,
      (∀ i z,(ψ i).val z=∑ j,(A.transpose)⁻¹ i j*(φ j).val z) ∧
      (∀ i,ScalarReplication P (W i) 0 (x i) (σ i) r 0 (σ i • ψ i) (M i)) ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → (∑ i,M i t w)=(∑ j,N j t w)) ∧
      ∀ i t w,geometricFlow (x i) r (σ i) ![t,(W i).W 0 (realTimeClamp t) w]=
        x i*Real.exp ((r-(∑ j,A i j^2)/2)*t+∑ j,A i j*B.W j (realTimeClamp t) w)

theorem basket_natural_self_financing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (T : ℝ) (hT : 0<T) [Fact (0≤T)]
    (hnatural : ∀ a : Icc (0:ℝ) T,B.F (realTimeClamp a.val)=Asakura.nullAugmentation P
      (MeasurableSpace.comap (fun w z => brownianTimeCoordinate P B a.val z w) inferInstance))
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hA : A.det≠0)
    (x wgt : Fin (d+1) → ℝ) (hx : ∀ i,0<x i) (hwgt : 0<wgt 0) (r K : ℝ) :
    let c := canonicalClock
    let hco := canonical_clock_properties.2.2.2.2.2
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
    let SF := fun φ N => BasketReplication P B A hA x r φ N
    letI := probability_trim P _ (B.le (realTimeClamp T))
    letI : MeasurableSpace Ω := B.F (realTimeClamp T)
    let Holding := fun i (t : Icc (0:ℝ) T) w => Real.exp (-r*(T-t.val))*wgt i/Stock i t.val w*
      R[(fun v => (if K<V v then (1:ℝ) else 0)*Stock i T v)|B.F (realTimeClamp t.val)] w
    ∃ H : Fin (d+1) → E,∃ N : Fin (d+1) → HalfClosedTime → Ω → ℝ,
      (∀ i,M2 (N i)) ∧ (∀ i,Ito i (H i) (N i)) ∧
      SF H N ∧
      Pay =ᵐ[P] (fun w => (∫ z,Pay z ∂R)+∑ i,N i (realTimeClamp T) w) ∧
      (∀ᵐ t ∂compactTimeMeasure T hT.le,∀ᵐ w ∂R,∀ i,
        Holding i t w=(∑ j,(A.transpose)⁻¹ i j*(H j).val (w,t.val))/(Real.exp (-r*t.val)*Stock i t.val w)) ∧
      ∀ᵐ t ∂compactTimeMeasure T hT.le,∀ᵐ w ∂R,∀ j,
        (∑ i,A i j*((Real.exp (-r*t.val)*Stock i t.val w)*Holding i t w))=restrict (H j) (w,t) := by
  have hgen (U : Lp ℝ 2 (P.trim (B.le (realTimeClamp T)))) :=
    vector_natural_information_on_trim P B T T le_rfl (hnatural ⟨T,hT.le,le_rfl⟩) U
      (Lp.stronglyMeasurable U).measurable
  have hnat (a : Icc (0:ℝ) T) (G : Ω → ℝ)
      (hG : Measurable[B.F (realTimeClamp a.val)] G) :=
    vector_natural_information_on_trim P B T a.val a.property.2 (hnatural a) G hG
  obtain ⟨hc,hcm,hct,hcut,hcc,hco⟩ := canonical_clock_properties
  have hmain := basket_black_scholes_clark_holdings P B canonicalClock hc hcm hct hcut hcc hco
    T hT hgen hnat A hA x wgt hx hwgt r K
  have hsf := basket_allocated_self_financing P B A hA x hx r
  dsimp only at hmain ⊢
  obtain ⟨φ,N,hN,hNI,hpay,hhold⟩ := hmain
  have hi j := (terminal_integrand_restriction P B.F B.mono B.le canonicalClock hco (φ j) T hT.le).2
  let R := P.trim (B.le (realTimeClamp T))
  letI := probability_trim P _ (B.le (realTimeClamp T))
  letI : MeasurableSpace Ω := B.F (realTimeClamp T)
  refine ⟨φ,N,hN,hNI,hsf φ N hN hNI,hpay,?_,hhold⟩
  apply basket_restricted_holdings R (compactTimeMeasure T hT.le) A hA
    (fun j z => (φ j).val (z.1,z.2.val)) hi
    (fun i z => ∑ j,(A.transpose)⁻¹ i j*(φ j).val (z.1,z.2.val)) (fun _ _ => rfl)
    _ _ _ hhold
  intro i t w
  exact mul_ne_zero (Real.exp_pos _).ne' (mul_pos (hx i) (Real.exp_pos _)).ne'


end Asakura.Chapter12
#print axioms Asakura.Chapter12.basket_natural_self_financing
