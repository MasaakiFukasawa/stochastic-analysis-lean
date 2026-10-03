import Chapter11OpenHarmonicIto
import Chapter11HeatBrownianCalculus
import Chapter11EuropeanAnalytic

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

noncomputable def europeanBrownianPrice (h : Ioi (0:ℝ) → ℝ) (s r σ T : ℝ) : (Fin 2 → ℝ) → ℝ :=
  brownianHeatPrice (fun q => ∫ z,logPayoff h z*heatLogKernel z q)
    (Real.exp (-r*T)) σ T (Real.log s+(r-σ^2/2)*T)

/-- The actual local stochastic integral of the discounted European price,
constructed on every closed interval strictly before maturity. -/
theorem european_price_ito_constructed {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h) (hn : ∀ x,0≤h x)
    (C m : ℝ) (hC : 0≤C) (hb : ∀ x,h x≤C*(1+x.val^m))
    (s r σ R T : ℝ) (hσ : σ≠0) (hR : 0≤R) (hRT : R<T) :
    ∃ N : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => fderiv ℝ (europeanBrownianPrice h s r σ T)
          ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,
            B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) N ∧
      ∀ t∈Icc 0 R,(fun w => europeanBrownianPrice h s r σ T ![t,B.W 0 (realTimeClamp t) w])=ᵐ[P]
        fun w => europeanBrownianPrice h s r σ T ![0,0]+N (realTimeClamp t) w := by
  obtain ⟨hfc,hfn,hfb⟩ := log_payoff_regular h hh hn C m hb
  let F := fun q => ∫ z,logPayoff h z*heatLogKernel z q
  have hF : ContDiffOn ℝ ∞ F {q | 0<q.1} := exponential_payoff_heat_smooth _ hfc.measurable hfn C m hC hfb
  have hv : ContDiffOn ℝ 2 (europeanBrownianPrice h s r σ T) {q | q 0<T} := by
    intro q hq
    exact (brownian_heat_smooth_at F hF _ σ T _ hσ q hq).contDiffWithinAt.of_le (by norm_num)
  have hp t (ht : t∈Icc 0 R) x := brownian_heat_harmonic F hF
    (fun a y ha => (exponential_payoff_heat_equation _ hfc.measurable hfn C m hC hfb a y ha).deriv)
    (Real.exp (-r*T)) σ T (Real.log s+(r-σ^2/2)*T) hσ t x (ht.2.trans_lt hRT)
  obtain ⟨N,hN,hNI,he⟩ := open_harmonic_ito_constructed P B R T hR hRT _ hv hp
  refine ⟨N,hN,hNI,?_⟩
  intro t ht
  filter_upwards [he t ht,(B.martingale 0).initial P B.F] with w hw hw0
  simpa only [hw0,Pi.zero_apply] using hw

/-- Along the geometric Brownian stock path, the Brownian-coordinate
function equals the discounted price constructed from the payoff. -/
theorem european_brownian_price_identity (h : Ioi (0:ℝ) → ℝ)
    (s r σ T t w : ℝ) (hs : 0<s) :
    europeanBrownianPrice h s r σ T ![t,w]=
      Real.exp (-r*t)*europeanHeatPrice h r σ (T-t) (s*Real.exp ((r-σ^2/2)*t+σ*w)) := by
  dsimp only [europeanBrownianPrice,brownianHeatPrice,europeanHeatPrice,heatPrice,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [Real.log_mul hs.ne' (Real.exp_ne_zero _),Real.log_exp,←mul_assoc,←Real.exp_add]
  congr 2 <;> ring

/-- The Brownian integrand is exactly discounted stock volatility times
the delta prescribed in the text. -/
theorem european_brownian_delta_identity (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h)
    (hn : ∀ x,0≤h x) (C m : ℝ) (hC : 0≤C) (hb : ∀ x,h x≤C*(1+x.val^m))
    (s r σ T t w : ℝ) (hs : 0<s) (hσ : σ≠0) (ht : t<T) :
    let S := s*Real.exp ((r-σ^2/2)*t+σ*w)
    fderiv ℝ (europeanBrownianPrice h s r σ T) ![t,w] (Pi.single 1 1)=
      Real.exp (-r*t)*σ*S*deriv (europeanHeatPrice h r σ (T-t)) S := by
  dsimp only
  let S := s*Real.exp ((r-σ^2/2)*t+σ*w)
  have hS : 0<S := mul_pos hs (Real.exp_pos _)
  obtain ⟨hfc,hfn,hfb⟩ := log_payoff_regular h hh hn C m hb
  let F := fun q => ∫ z,logPayoff h z*heatLogKernel z q
  have hF : ContDiffOn ℝ ∞ F {q | 0<q.1} := exponential_payoff_heat_smooth _ hfc.measurable hfn C m hC hfb
  have hτ : 0<σ^2*(T-t) := mul_pos (sq_pos_of_ne_zero hσ) (sub_pos.mpr ht)
  have hFa a : ContDiffAt ℝ ∞ F (σ^2*(T-t),a) := hF.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds hτ)
  have hFs : ContDiff ℝ ∞ (fun a => F (σ^2*(T-t),a)) := by
    rw [contDiff_iff_contDiffAt]
    intro a
    exact (hFa a).comp a (contDiffAt_const.prodMk contDiffAt_id)
  have hlog : Real.log S+(r-σ^2/2)*(T-t)=Real.log s+(r-σ^2/2)*T+σ*w := by
    dsimp only [S]
    rw [Real.log_mul hs.ne' (Real.exp_ne_zero _),Real.log_exp]
    ring
  change fderiv ℝ (brownianHeatPrice F (Real.exp (-r*T)) σ T (Real.log s+(r-σ^2/2)*T)) ![t,w] (Pi.single 1 1)=
    Real.exp (-r*t)*σ*S*deriv (heatPrice F r σ (T-t)) S
  rw [brownian_heat_first F hF _ σ T _ hσ _ _ (by simpa using ht),
    (heat_price_dx F r σ (T-t) S hS hFs).deriv,hlog]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (0:Fin 2)≠1),mul_zero,mul_one]
  rw [show ((0:ℝ),σ)=σ • (0,1) by ext <;> simp,map_smul,smul_eq_mul]
  have hd := (scalar_space_slice_derivative F (σ^2*(T-t)) (Real.log s+(r-σ^2/2)*T+σ*w) (hFa _)).deriv
  simp only [iteratedFDeriv_one_apply] at hd
  rw [←hd]
  have he : Real.exp (-r*t)*Real.exp (-r*(T-t))=Real.exp (-r*T) := by rw [←Real.exp_add];congr 1;ring
  rw [←he]
  field_simp [hS.ne'] <;> ring

end Asakura.Chapter11
