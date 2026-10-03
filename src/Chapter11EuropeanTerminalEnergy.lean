import Chapter11EuropeanPrefixEnergy
import Chapter11TerminalEnergy

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

lemma positive_interval_exhaustion (T : ℝ) (hT : 0<T) :
    ∃ c : ℕ → ℝ,(∀ n,0<c n) ∧ Monotone c ∧ (∀ n,c n<T) ∧ (⋃ n,Ioc (0:ℝ) (c n))=Ioo 0 T := by
  letI : Fact (0≤(T:EReal)) := ⟨by exact_mod_cast hT.le⟩
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion (T:=(T:EReal)) (by exact_mod_cast hT)
  have hcT' n : c n<T := EReal.coe_lt_coe_iff.mp (hcT n)
  refine ⟨c,hc,hcm.monotone,hcT',?_⟩
  ext r
  simp only [mem_iUnion,mem_Ioc,mem_Ioo]
  constructor
  · rintro ⟨n,hr,hrc⟩
    exact ⟨hr,hrc.trans_lt (hcT' n)⟩
  · rintro ⟨hr,hrT⟩
    have hrt : realTimeClamp (T:=(T:EReal)) r<⊤ := by
      change (realTimeClamp (T:=(T:EReal)) r:EReal)<T
      rw [real_time_clamp_eq r hr.le (EReal.coe_le_coe hrT.le)]
      exact EReal.coe_lt_coe_iff.mpr hrT
    obtain ⟨n,hn⟩ := hcc _ hrt
    change (realTimeClamp (T:=(T:EReal)) r:EReal)<(realTimeClamp (T:=(T:EReal)) (c n):EReal) at hn
    rw [real_time_clamp_eq r hr.le (EReal.coe_le_coe hrT.le),real_time_clamp_eq (c n) (hc n).le (hcT n).le] at hn
    exact ⟨n,hr,(EReal.coe_lt_coe_iff.mp hn).le⟩

/-- The actual European delta has finite total energy up to maturity,
obtained from the preterminal Ito formulas and monotone convergence. -/
theorem european_delta_terminal_energy {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h) (hn : ∀ x,0≤h x)
    (C m : ℝ) (hC : 0≤C) (hb : ∀ x,h x≤C*(1+x.val^m))
    (s r σ T : ℝ) (hs : 0<s) (hσ : 0<σ) (hT : 0<T)
    (M : HalfClosedTime → Ω → ℝ) (hM : ContinuousM2Witness P B.F M) (a : ℝ)
    (hrep : ∀ t,(fun w => a+M t w)=ᵐ[P]
      P[(fun w => Real.exp (-r*T)*h ⟨s*Real.exp ((r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w),mul_pos hs (Real.exp_pos _)⟩)|B.F t]) :
    let H := fun z : Ω × ℝ => fderiv ℝ (europeanBrownianPrice h s r σ T)
      ![z.2,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)
    Integrable (fun z => (H z)^2) (P.prod (volume.restrict (Ioo 0 T))) ∧
      (∫ z,(H z)^2 ∂P.prod (volume.restrict (Ioo 0 T)))≤∫ w,(M ⊤ w)^2 ∂P := by
  dsimp only
  let H := fun z : Ω × ℝ => fderiv ℝ (europeanBrownianPrice h s r σ T)
    ![z.2,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)
  have hH : Measurable H := by
    apply (measurable_fderiv_apply_const (𝕜:=ℝ) (f:=europeanBrownianPrice h s r σ T) (Pi.single 1 1)).comp
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact measurable_snd
    · exact half_local_joint_measurable P B.F B.le (B.W 0) (B.martingale 0)
  obtain ⟨c,hc,hcm,hcT,hu⟩ := positive_interval_exhaustion T hT
  have hpref R (hR : 0≤R) (hRT : R<T) :
      (∀ w,IntervalIntegrable (fun t => H (w,t)^2) volume 0 R) ∧
      Integrable (fun w => ∫ t in 0..R,H (w,t)^2) P ∧
      (∫ w,(∫ t in 0..R,H (w,t)^2) ∂P)≤∫ w,(M ⊤ w)^2 ∂P := by
    obtain ⟨N,hN,hNI,he,hE,hbE⟩ := european_delta_prefix_energy P B h hh hn C m hC hb s r σ R T hs hσ hR hRT M hM a hrep
    let G := fun z : Ω × ℝ => fderiv ℝ (europeanBrownianPrice h s r σ T)
      ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)
    have heg w t (ht : t∈Icc 0 R) : G (w,t)=H (w,t) := by
      dsimp only [G,H]
      rw [finite_prefix_time_of_real R t hR ht le_top]
    have hei w : (∫ t in 0..R,G (w,t)^2)=∫ t in 0..R,H (w,t)^2 :=
      intervalIntegral.integral_congr (fun t ht => by rw [heg w t (by simpa [uIcc_of_le hR] using ht)])
    have hpath w : IntervalIntegrable (fun t => H (w,t)^2) volume 0 R := by
      have hvm : ContDiffOn ℝ 2 (europeanBrownianPrice h s r σ T) {q | q 0<T} := by
        obtain ⟨hfc,hfn,hfb⟩ := log_payoff_regular h hh hn C m hb
        have hF := exponential_payoff_heat_smooth _ hfc.measurable hfn C m hC hfb
        intro q hq
        exact (brownian_heat_smooth_at _ hF _ σ T _ hσ.ne' q hq).contDiffWithinAt.of_le (by norm_num)
      obtain ⟨_,_,hi⟩ := open_price_gradient_regularity P B R T hR hRT _ hvm
      by_cases hR0 : R=0
      · subst R;simp
      have hpos : 0<R := lt_of_le_of_ne hR (Ne.symm hR0)
      apply (hi R hpos w).congr
      intro t ht
      have ht' : t∈Ioc 0 R := by simpa [uIoc_of_le hR] using ht
      change G (w,t)^2=H (w,t)^2
      rw [heg w t ⟨ht'.1.le,ht'.2⟩]
    exact ⟨hpath,by simpa only [G,hei] using hE,by simpa only [G,hei] using hbE⟩
  exact terminal_square_energy_from_prefix_bounds P H hH T _ c (fun n => (hc n).le) hcm hu
    (fun n => ae_of_all _ (hpref (c n) (hc n).le (hcT n)).1)
    (fun n => (hpref (c n) (hc n).le (hcT n)).2.1)
    (fun n => (hpref (c n) (hc n).le (hcT n)).2.2)

end Asakura.Chapter11
