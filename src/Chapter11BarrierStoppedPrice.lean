import Chapter11BarrierAnalytic
import Chapter11StoppedHarmonic

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The actual image price is uniformly bounded in Brownian coordinates
on the pre-knockout region. -/
theorem image_brownian_price_bounds (f : ℝ → ℝ) (hf : Measurable f)
    (K ν r σ T y0 t x : ℝ) (hK : 0≤K) (hn : ∀ z,0≤f z) (hb : ∀ z,f z≤K)
    (hz : ∀ z,0<z → f z=0) (hσ : σ≠0) (hν : ν*σ^2=2*r-σ^2)
    (ht : t<T) (hy : y0+(r-σ^2/2)*t+σ*x≤0) :
    let V := brownianHeatPrice (imageHeat f ν) (Real.exp (-r*T)) σ T (y0+(r-σ^2/2)*T) ![t,x]
    0≤V ∧ V≤Real.exp (-r*T)*K := by
  let a := r-σ^2/2
  let y := y0+a*t+σ*x
  let v := σ^2*(T-t)
  have hv : 0<v := mul_pos (sq_pos_of_ne_zero hσ) (sub_pos.mpr ht)
  have hp : ν*v=2*a*(T-t) := by dsimp [v,a];linear_combination (T-t)*hν
  have hmean : y0+a*T+σ*x=y+a*(T-t) := by dsimp [y];ring
  have hi := image_heat_gaussian_formula f a (T-t) ν y v hv hp
  have hvar : (NNReal.mk v hv.le)≠0 := by intro h;have hh := congrArg (fun q : ℝ≥0 => (q:ℝ)) h;exact hv.ne' hh
  obtain ⟨hlo,hmid,hup⟩ := barrier_image_integral_bounds a (T-t) ν y (NNReal.mk v hv.le) hvar hp hy f hf K hK hn hb hz
  dsimp only [brownianHeatPrice,Matrix.cons_val_zero,Matrix.cons_val_one]
  change 0≤Real.exp (-r*T)*imageHeat f ν (v,y0+a*T+σ*x) ∧ _
  rw [hmean,hi]
  exact ⟨mul_nonneg (Real.exp_pos _).le hlo,mul_le_mul_of_nonneg_left (hmid.trans hup) (Real.exp_pos _).le⟩

/-- Apply the constructed Ito formula to the concrete image price,
then stop in the region below the barrier. Only the stopping-time and
path-bound properties of the first hitting time remain as inputs here. -/
theorem image_price_stopped_integral {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (f : ℝ → ℝ) (hf : Measurable f) (K ν r σ T R y0 : ℝ)
    (hK : 0≤K) (hn : ∀ z,0≤f z) (hb : ∀ z,f z≤K) (hz : ∀ z,0<z → f z=0)
    (hσ : σ≠0) (hν : ν*σ^2=2*r-σ^2) (hR : 0≤R) (hRT : R<T)
    (τ : Ω → Icc (0:ℝ) R)
    (hτ : ∀ t,MeasurableSet[B.F t] {w | realTimeClamp (τ w).val≤t})
    (hregion : ∀ᵐ w ∂P,∀ t∈Icc 0 R,
      y0+(r-σ^2/2)*min (τ w).val t+σ*B.W 0 (realTimeClamp (min (τ w).val t)) w≤0) :
    let v := brownianHeatPrice (imageHeat f ν) (Real.exp (-r*T)) σ T (y0+(r-σ^2/2)*T)
    ∃ N : HalfClosedTime → Ω → ℝ,ContinuousM2Witness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => (Ioc (⊥ : HalfClosedTime) (realTimeClamp (τ z.1).val)).indicator
          (fun _ => fderiv ℝ v ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,
            B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) (realTimeClamp z.2)) N ∧
      ∀ᵐ w ∂P,∀ t∈Icc 0 R,
        v ![min (τ w).val t,B.W 0 (realTimeClamp (min (τ w).val t)) w]=
          v ![0,B.W 0 ⊥ w]+N (realTimeClamp t) w := by
  dsimp only
  obtain ⟨hs,hv,hp⟩ := image_heat_smooth_harmonic f hf K ν (Real.exp (-r*T)) σ T (y0+(r-σ^2/2)*T) hK hn hb hσ
  apply bounded_stopped_harmonic_integral P B R T hR hRT _ hv
    (fun t ht x => hp t x (ht.2.trans_lt hRT)) τ hτ (Real.exp (-r*T)*K)
  filter_upwards [hregion] with w hw
  intro t ht
  have hh := image_brownian_price_bounds f hf K ν r σ T y0 (min (τ w).val t)
    (B.W 0 (realTimeClamp (min (τ w).val t)) w) hK hn hb hz hσ hν
    ((min_le_right _ _).trans_lt (ht.2.trans_lt hRT)) (hw t ht)
  rw [abs_of_nonneg hh.1]
  exact hh.2

end Asakura.Chapter11
