import Chapter12AsianCallTimeKernel

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem asian_discounted_hedge_identity (r T t σ S V : ℝ) (hT : T≠0) (hσ : σ≠0) (hS : S≠0) :
    ((Real.exp (-r*T)*σ/T)*V)/(σ*Real.exp (-r*t)*S)=Real.exp (-r*(T-t))/(T*S)*V := by
  have he : Real.exp (-r*(T-t))=Real.exp (-r*T)/Real.exp (-r*t) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he]
  field_simp
  <;> ring

/-- Substituting the verified Asian payoff derivative into the timewise
Clark integrand yields precisely the printed holdings coefficient. -/
theorem asian_clark_holdings_coefficient {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0<T)
    (F : Icc (0:ℝ) T → MeasurableSpace Ω)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (x σ r K : ℝ) (hx : 0<x) (hσ : 0<σ)
    (φ dF : Ω × Icc (0:ℝ) T → ℝ)
    (hφ : ∀ᵐ t ∂compactTimeMeasure T hT.le,
      (fun w => φ (w,t)) =ᵐ[P] P[(fun w => dF (w,t))|F t])
    (hd : dF =ᵐ[P.prod (compactTimeMeasure T hT.le)]
      (fun z => (Real.exp (-r*T)*σ/T)*(if K<asianPathAverage x r T hT.le σ (X z.1) then (1:ℝ) else 0)*
        asianRemainingMoment T hT.le x σ r 0 (X z.1) z.2)) :
    ∀ᵐ t ∂compactTimeMeasure T hT.le,∀ᵐ w ∂P,
      φ (w,t)/(σ*Real.exp (-r*t.val)*stockPathValue x σ r T (X w) t)=
        Real.exp (-r*(T-t.val))/(T*stockPathValue x σ r T (X w) t)*
          P[(fun v => (if K<asianPathAverage x r T hT.le σ (X v) then (1:ℝ) else 0)*
            asianRemainingMoment T hT.le x σ r 0 (X v) t)|F t] w := by
  have hds := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := compactTimeMeasure T hT.le) (ν := P)).quasiMeasurePreserving.ae hd)
  filter_upwards [hφ,hds] with t ht hdt
  let Y := fun w => (if K<asianPathAverage x r T hT.le σ (X w) then (1:ℝ) else 0)*
    asianRemainingMoment T hT.le x σ r 0 (X w) t
  let c := Real.exp (-r*T)*σ/T
  have he : (fun w => dF (w,t)) =ᵐ[P] (fun w => c*Y w) := by
    filter_upwards [hdt] with w hw
    change dF (w,t)=_ at hw
    simpa only [c,Y,Prod.swap, mul_assoc] using hw
  have hce := condExp_congr_ae (m := F t) he
  have hsc := condExp_smul c Y (F t) (μ := P)
  filter_upwards [ht,hce,hsc] with w hw hc hs
  rw [hw,hc]
  change P[(c • Y)|F t] w/(σ*Real.exp (-r*t.val)*stockPathValue x σ r T (X w) t)=_
  rw [hs]
  change (c*P[Y|F t] w)/(σ*Real.exp (-r*t.val)*stockPathValue x σ r T (X w) t)=_
  exact asian_discounted_hedge_identity r T t.val σ _ _ hT.ne' hσ.ne'
    (mul_pos hx (Real.exp_pos _)).ne'

end Asakura.Chapter12
