import Chapter4LevyConstructed
import Chapter4GeometricGlobal
import Chapter4GaussianPayoff

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The Gaussian law used in the pricing calculation is derived from the
actual Brownian local martingale and its bracket, not assumed for a terminal
random variable. -/
theorem brownian_standardized_law
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0<R) (hRT : (R:EReal)<T) :
    HasLaw (fun w => W (realTimeClamp R) w/Real.sqrt R) (gaussianReal 0 1) P := by
  have hz : realTimeClamp (T := T) 0=⊥ := by
    apply Subtype.ext
    change (realTimeClamp (T := T) 0:EReal)=0
    simpa only [EReal.coe_zero] using real_time_clamp_eq (T := T) 0 le_rfl (show (0:EReal)≤T from Fact.out)
  have hl := (levy_gaussian_increment_constructed P hT F hF hle hnull W A hW hA hclock
    R hR.le hRT 0 ⟨le_rfl,hR.le⟩).1
  have he : W (realTimeClamp R)=ᵐ[P] fun w => W (realTimeClamp R) w-W (realTimeClamp 0) w := by
    filter_upwards [hW.initial P F] with w hw
    simp only [hz,hw,Pi.zero_apply,sub_zero]
  have hlw := hl.congr he
  have hn := gaussianReal_div_const hlw (Real.sqrt R)
  convert hn using 1
  congr 1
  · simp only [zero_div]
  · apply NNReal.eq
    simp only [NNReal.coe_div,NNReal.coe_mk,NNReal.coe_one,sub_zero,Real.sq_sqrt hR.le]
    exact (div_self hR.ne').symm

/-- Both Black--Scholes payoff identities for the explicit geometric solution.
Its SDE is proved in geometric_sde_global; Chapter4NormalCDF supplies the PDE
and derivative verification. -/
theorem black_scholes_constructed_payoffs
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (t : ℝ),0≤t → (t:EReal)<T → A (realTimeClamp t) w=t)
    (s K r q σ R : ℝ) (hs : 0<s) (hK : 0<K) (hσ : 0<σ) (hR : 0<R) (hRT : (R:EReal)<T) :
    (∫ w,Real.exp (-r*R)*max 0 (geometricFlow s (r-q) σ ![R,W (realTimeClamp R) w]-K) ∂P)=bsCall K r q σ s R ∧
    (∫ w,Real.exp (-r*R)*max 0 (K-geometricFlow s (r-q) σ ![R,W (realTimeClamp R) w]) ∂P)=bsPut K r q σ s R := by
  have hl := brownian_standardized_law P hT F hF hle hnull W A hW hA hclock R hR hRT
  have hh := bs_payoffs_of_normal_law P _ hl s K r q σ R hs hK hσ hR
  have he w : geometricFlow s (r-q) σ ![R,W (realTimeClamp R) w]=
      s*Real.exp ((r-q-σ^2/2)*R+σ*Real.sqrt R*(W (realTimeClamp R) w/Real.sqrt R)) := by
    dsimp only [geometricFlow,Matrix.cons_val_zero,Matrix.cons_val_one]
    congr 2
    field_simp [Real.sqrt_ne_zero'.mpr hR]
  simpa only [←he] using hh

end Asakura.Chapter4
