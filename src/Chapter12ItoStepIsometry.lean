import Chapter12BoundedStepEnergy
import Chapter12ItoBoundedStepIdentity

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Identification of a step vector in the actual chapter-5 isometry.
Its output is the centered weighted Brownian increment, not an abstract
symbol for a stochastic integral. -/
theorem actual_ito_step_isometry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (c : ℕ → ℝ)
    (I : progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hI : ∀ H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) H.val N ∧
        I ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩ = (hN.moment ⊤).toLp (N ⊤))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (G : Ω → ℝ) (hGm : Measurable[B.F (realTimeClamp a)] G) (hG : MemLp G ∞ P) :
    let H := boundedStepEnergy P B.F B.mono B.le c a b G hGm hG
    let v : progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))) :=
      ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩
    ((I v : Ω → ℝ) =ᵐ[P] fun w => G w*(B.W i (realTimeClamp b) w-B.W i (realTimeClamp a) w)) ∧
      (∫ w,I v w ∂P)=0 := by
  dsimp only
  let H := boundedStepEnergy P B.F B.mono B.le c a b G hGm hG
  obtain ⟨N,hN,hNI,he⟩ := hI H
  have ht := bounded_step_ito_terminal_identity P B i a b ha hab G hGm hG N hN hNI
  have hm := integral_congr_ae ((hN.martingale ⊥ ⊤ bot_le).trans hN.initial)
  rw [integral_condExp (B.le ⊥)] at hm
  have hm0 : (∫ w,N ⊤ w ∂P)=0 := by simpa using hm
  constructor
  · rw [he]
    exact (hN.moment ⊤).coeFn_toLp.trans ht
  · rw [he]
    exact (integral_congr_ae (hN.moment ⊤).coeFn_toLp).trans hm0

end Asakura.Chapter12
