import Chapter7ContinuousItoClockDensity
import Chapter4ConstructedScalarIto
import Chapter5TimeDensityVariation
import Chapter2ItoAssociativity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- A C² change of a constructed drift-free diffusion, with both the
new Ito integral and the ordinary drift integral identified explicitly. -/
theorem scalar_diffusion_transform
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (Y : HalfClosedTime → Ω → ℝ)
    (hY : LocalMProcessWitness P B.F Y)
    (σ : ℝ → ℝ) (hσ : Continuous σ)
    (hI : ItoCovarianceFormula P B.F (B.W 0) (fun z => σ (Y (realTimeClamp z.2) z.1)) Y)
    (f f1 f2 : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hd : ∀ x,HasDerivAt f (f1 x) x) (hdd : ∀ x,HasDerivAt f1 (f2 x) x) :
    ∃ Z : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F Z ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => f1 (Y (realTimeClamp z.2) z.1)*σ (Y (realTimeClamp z.2) z.1)) Z ∧
      ∀ r : ℝ,0 ≤ r → (fun w => f (Y (realTimeClamp r) w)) =ᵐ[P]
        fun w => f 0+Z (realTimeClamp r) w+
          (∫ s in 0..r,f2 (Y (realTimeClamp s) w)*(σ (Y (realTimeClamp s) w))^2)/2 := by
  have hT : (0:EReal) < ⊤ := by simp
  have hfin r : realTimeClamp (T := (⊤:EReal)) r < ⊤ :=
    lt_of_le_of_lt (real_time_clamp_mono (le_max_right 0 r)) (changed_time_finite _ (le_max_left _ _))
  have hYc w : Continuous (fun r => Y (realTimeClamp r) w) := continuous_iff_continuousAt.mpr
    (fun r => (hY.path P B.F w _ (hfin r)).comp real_time_clamp_continuous.continuousAt)
  have hd1 : deriv f = f1 := funext fun x => (hd x).deriv
  have hd2 : iteratedDeriv 2 f = f2 := by
    rw [show (2:ℕ) = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,hd1]
    exact funext fun x => (hdd x).deriv
  have h1c : Continuous f1 := hd1 ▸ hf.continuous_deriv (by norm_num)
  have h2c : Continuous f2 := hd2 ▸ hf.continuous_iteratedDeriv 2 le_rfl
  let H := fun z : Ω × ℝ => σ (Y (realTimeClamp z.2) z.1)
  let H1 := fun z : Ω × ℝ => f1 (Y (realTimeClamp z.2) z.1)
  let H2 := fun z : Ω × ℝ => f2 (Y (realTimeClamp z.2) z.1)
  have hHc w : Continuous (fun r => H (w,r)) := hσ.comp (hYc w)
  have hH1c w : Continuous (fun r => H1 (w,r)) := h1c.comp (hYc w)
  have hH2c w : Continuous (fun r => H2 (w,r)) := h2c.comp (hYc w)
  obtain ⟨C,hC,hCd⟩ := continuous_ito_clock_density P B Y hY H hHc hI
  obtain ⟨c,hcp,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  let hc := fun n => (hcp n).le
  obtain ⟨N,J,hN,hNI,hJI,he⟩ := constructed_local_ito P hT B.F B.mono B.le B.null
    Y C hY hC f f1 f2 hf hd hdd c hc hcm.monotone hcT hcc
  obtain ⟨Z,hZ,hZI⟩ := continuous_adapted_ito_exists P hT B.F B.mono B.le B.null
    (B.W 0) (B.martingale 0) (fun z => H1 z*H z)
    (fun r _ _ => (h1c.measurable.comp (hY.adapted P B.F _ (hfin r))).mul
      (hσ.measurable.comp (hY.adapted P B.F _ (hfin r))))
    (fun b _ _ w => ((hH1c w).mul (hHc w)).continuousOn)
  have hNZ := ito_integral_associativity P hT B.F B.mono B.le B.null
    (B.W 0) Y N Z H H1 (B.martingale 0) hY hN hZ
    (fun w => (hHc w).measurable) (fun w => (hH1c w).measurable) hI hNI hZI
  refine ⟨Z,hZ,hZI,?_⟩
  intro r hr
  have hJr := time_density_variation_integral P C J (fun z => (H z)^2) H2 c hc hcT hcc
    (fun n => hCd (c n) (hc n)) (fun w => ((hHc w).pow 2).measurable)
    (fun n => ae_of_all _ fun w => ((hHc w).pow 2).intervalIntegrable 0 (c n))
    (fun w => (hH2c w).measurable) (fun n w => (hH2c w).continuousOn) hJI r hr (EReal.coe_lt_top r)
  filter_upwards [he,hNZ,hJr,hY.initial P B.F] with w hew hNZw hJw hY0
  have hh := hew (realTimeClamp r) (changed_time_finite r hr)
  rw [hY0,hNZw _ (changed_time_finite r hr),hJw] at hh
  exact hh

end Asakura.Chapter7
