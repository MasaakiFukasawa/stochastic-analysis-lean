import Chapter12ItoReverseAssociativity
import Chapter12CanonicalClock
import Chapter4BrownianSystem
import Chapter3OpenPathMeasurable
import Chapter4GeometricGlobal

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Actual discounted stock gains for any Brownian representation. Both
stock integral and holdings integral are constructed, with no integral-existence
assumption on the latter. -/
theorem scalar_stock_gains {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (x σ : ℝ) (hx : x≠0) (hσ : σ≠0)
    (φ : Ω × ℝ → ℝ) (hφ : Measurable φ)
    (N : HalfClosedTime → Ω → ℝ) (hN : ContinuousM2Witness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W i) φ N) :
    let Sd := fun z : Ω × ℝ => geometricFlow x 0 σ
      ![B.C i i (realTimeClamp z.2) z.1,B.W i (realTimeClamp z.2) z.1]
    ∃ Y : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F Y ∧
      ItoCovarianceFormula P B.F (B.W i) (fun z => σ*Sd z) Y ∧
      ItoCovarianceFormula P B.F Y (fun z => φ z/(σ*Sd z)) N ∧
      ∀ᵐ w ∂P,∀ t : ℝ,0≤t →
        geometricFlow x 0 σ ![t,B.W i (realTimeClamp t) w]=x+Y (realTimeClamp t) w := by
  intro Sd
  obtain ⟨Y,hY,hYI,he⟩ := geometric_sde_global P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W i) (B.C i i) (B.martingale i) (B.cov i i)
    (fun w t ht _ => B.diagonal_clock i w t ht) x 0 σ
  obtain ⟨hc,hcm,hct,hcut,hcc,hco⟩ := canonical_clock_properties
  have hNl := continuous_m2_is_local P B.F B.mono B.le
    (fun n => realTimeClamp (T:=⊤) (canonicalClock n)) hct.monotone hcut hcc N hN
  have hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<⊤ → B.C i i (realTimeClamp r) w=r :=
    fun w r hr _ => B.diagonal_clock i w r hr
  have hSm w : Measurable (fun t => Sd (w,t)) := by
    apply (geometricFlow_smooth x 0 σ).continuous.measurable.comp
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j
    · exact open_path_real_measurable _ ((clock_regular_from_identity (B.C i i) hclock).2 w)
    · exact open_path_real_measurable _ ((B.martingale i).path P B.F w)
  have hS0 z : Sd z≠0 := by
    dsimp [Sd,geometricFlow]
    exact mul_ne_zero hx (Real.exp_ne_zero _)
  have hprod : (fun z => (φ z/(σ*Sd z))*(σ*Sd z))=φ := by
    funext z
    exact div_mul_cancel₀ _ (mul_ne_zero hσ (hS0 z))
  have hI := ito_reverse_associativity P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W i) Y N (fun z => σ*Sd z) (fun z => φ z/(σ*Sd z))
    (B.martingale i) hY hNl (fun w => (hSm w).const_mul σ)
    (fun w => (hφ.comp (measurable_const.prodMk measurable_id)).div ((hSm w).const_mul σ))
    hYI (by rw [hprod];exact hNI)
  refine ⟨Y,hY,hYI,hI,?_⟩
  filter_upwards [he] with w hw
  intro t ht
  simpa only [zero_mul,add_zero] using hw t ht (EReal.coe_lt_top t)

end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_stock_gains
