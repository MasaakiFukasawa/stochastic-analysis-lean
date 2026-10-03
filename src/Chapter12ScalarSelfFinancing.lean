import Chapter12ScalarStrategyDomains
import Chapter12ConstantRateBankIntegral
import Chapter12DiscountedReplicationGains

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter11
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem scalar_hedge_self_financing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : BrownianSystem P d)
    (i : Fin d) (x σ r v : ℝ) (hx : 0<x) (hσ : σ≠0)
    (φ : progressiveEnergyIntegrands W.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ)))))
    (N : HalfClosedTime → Ω → ℝ) (hN : ContinuousM2Witness P W.F N)
    (hNI : ItoCovarianceFormula P W.F (W.W i) φ.val N) :
    let S := fun z : Ω × ℝ => geometricFlow x r σ ![z.2,W.W i (realTimeClamp z.2) z.1]
    let H := fun z => φ.val z/(σ*(Real.exp (-r*z.2)*S z))
    let η := fun z : Ω × ℝ => v+N (realTimeClamp z.2) z.1-φ.val z/σ
    let B := fun t w => Real.exp (r*W.C i i t w)
    ∃ Y A M G E : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P W.F Y ∧ AdaptedLocalVariationWitness W.F A ∧
      LocalMProcessWitness P W.F M ∧ AdaptedLocalVariationWitness W.F E ∧
      (∀ᵐ w ∂P,∀ t : ℝ,0≤t → S (w,t)=(x+Y (realTimeClamp t) w)*B (realTimeClamp t) w) ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → (x+Y t w)*B t w=(x+Y ⊥ w)*B ⊥ w+A t w+M t w) ∧
      SemimartingaleIntegralFormula P W.F canonicalClock (fun n => (canonical_clock_properties.1 n).le) A M H G ∧
      VariationIntegralFormula P canonicalClock (fun n => (canonical_clock_properties.1 n).le) B η E ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → (v+N t w)*B t w=(v+N ⊥ w)*B ⊥ w+G t w+E t w) ∧
      (∀ w t,H (w,t)*S (w,t)+η (w,t)*Real.exp (r*t)=Real.exp (r*t)*(v+N (realTimeClamp t) w)) := by
  intro S H η B
  obtain ⟨Y,hY,hHY,hSd,hportfolio,hdom⟩ := scalar_replication_domains P W i x σ r v hx hσ φ N hN hNI
  have hηm w : Measurable (fun t => η (w,t)) :=
    (measurable_const.add (open_path_real_measurable _ (fun t _ => (hN.path w).continuousAt))).sub
      ((φ.property.1.comp measurable_prodMk_left).div_const σ)
  have hNp n := continuous_adapted_real_progressive W.F W.mono
    (fun z : Ω × ℝ => N (realTimeClamp z.2) z.1) (canonicalClock n) (canonical_clock_properties.1 n).le
    (fun t _ => hN.adapted _) (fun w => ((hN.path w).comp real_time_clamp_continuous).continuousOn)
  have hηp n : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (canonicalClock n) => W.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (canonicalClock n) => η (z.1,z.2.val)) :=
    (measurable_const.add (hNp n)).sub ((φ.property.2.1 n).div_const σ)
  obtain ⟨hB,hBc,E,hE,hEc,hEI⟩ := constant_rate_bank_integral P W i r η hηm hηp
    (fun n => hdom.mono (fun w hw => (hw (canonicalClock n) (canonical_clock_properties.1 n).le).2.2))
  have hHm w : Measurable (fun t => H (w,t)) := by
    have hφ := φ.property.1.comp (measurable_prodMk_left (x := w))
    have hw := open_path_real_measurable _ ((W.martingale i).path P W.F w)
    dsimp only [H,S,geometricFlow]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    exact hφ.div (measurable_const.mul
      (((measurable_const.mul measurable_id).exp).mul
        (measurable_const.mul (((measurable_const.mul measurable_id).add
          (measurable_const.mul hw)).exp))))
  obtain ⟨hc,hcm,hct,hcut,hcc,hco⟩ := canonical_clock_properties
  have hNl := continuous_m2_is_local P W.F W.mono W.le
    (fun n => realTimeClamp (T:=⊤) (canonicalClock n)) hct.monotone hcut hcc N hN
  have hbal : ∀ᵐ w ∂P,∀ t : ℝ,0≤t → (t:EReal)<⊤ →
      v+N (realTimeClamp t) w=H (w,t)*(x+Y (realTimeClamp t) w)+η (w,t) := by
    filter_upwards [hSd] with w hw
    intro t ht _
    rw [← hw t ht]
    dsimp only [H,η]
    have hs : S (w,t)≠0 := by dsimp [S,geometricFlow];positivity
    have hd : Real.exp (-r*t)≠0 := (Real.exp_pos _).ne'
    field_simp
    <;> ring
  obtain ⟨A,M,G,hA,hM,hstock,hG,hwealth⟩ := discounted_replication_original_gains P
    (by simp : (0:EReal)<⊤) W.F W.mono W.le W.null canonicalClock (fun n => (hc n).le)
    hcm.monotone (fun _ => EReal.coe_lt_top _) hcc Y N B E x v H η hY hNl hHm hHY
    hB hBc hE hEc hEI hbal
  refine ⟨Y,A,M,G,E,hY,hA,hM,hE,?_,hstock,hG,hEI,hwealth,hportfolio⟩
  filter_upwards [hSd] with w hw
  intro t ht
  rw [← hw t ht]
  dsimp only [B]
  rw [W.diagonal_clock i w t ht]
  have he : Real.exp (-r*t)*Real.exp (r*t)=1 := by rw [←Real.exp_add];simp
  calc
    S (w,t) = S (w,t)*1 := by ring
    _ = (Real.exp (-r*t)*S (w,t))*Real.exp (r*t) := by rw [←he];ring

end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_hedge_self_financing
