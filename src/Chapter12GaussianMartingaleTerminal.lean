import Chapter12WienerItoGaussian

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem finite_sum_continuous_m2 {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (N : ι → HalfClosedTime → Ω → ℝ) (hN : ∀ i, ContinuousM2Witness P F (N i)) :
    ContinuousM2Witness P F (fun t w => ∑ i, N i t w) := by
  classical
  have hs (s : Finset ι) : ContinuousM2Witness P F (fun t w => ∑ i ∈ s, N i t w) := by
    induction s using Finset.induction_on with
    | empty =>
      convert ContinuousM2Witness.zero P F using 1 <;> ext t w <;> simp
    | @insert i s hi ih =>
      convert (hN i).add P F ih using 1 <;> ext t w <;> simp [Finset.sum_insert hi]
  exact hs Finset.univ

/-- Gaussianity and centering pass to the actual terminal L2 limit of a
continuous M2 martingale, including an infinite terminal time. -/
theorem centered_gaussian_m2_terminal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (M : HalfClosedTime → Ω → ℝ) (hM : ContinuousM2Witness P F M)
    (hlaw : ∀ t : HalfClosedTime, t < ⊤ → HasGaussianLaw (M t) P ∧ (∫ w,M t w ∂P)=0) :
    HasGaussianLaw ((hM.moment ⊤).toLp (M ⊤) : Ω → ℝ) P ∧
      (∫ w,(hM.moment ⊤).toLp (M ⊤) w ∂P)=0 := by
  obtain ⟨u,_,hum,hut⟩ := exists_seq_strictMono_tendsto'
    (show (⊥ : HalfClosedTime)<⊤ from (show (0:EReal)<⊤ by simp))
  let Z := fun n => (hM.moment (u n)).toLp (M (u n))
  have hlim : Tendsto Z atTop (𝓝 ((hM.moment ⊤).toLp (M ⊤))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
      ((continuous_m2_time_l2_continuity P F hF hle M hM ⊤).comp hut)
  refine ⟨Asakura.gaussian_L2_limit (fun n =>
    ((hlaw (u n) (hum n).2).1).congr (hM.moment (u n)).coeFn_toLp.symm) hlim,?_⟩
  have hmean := Asakura.L2_mean_continuous.continuousAt.tendsto.comp hlim
  have hz n : (∫ w,Z n w ∂P)=0 :=
    (integral_congr_ae (hM.moment (u n)).coeFn_toLp).trans (hlaw (u n) (hum n).2).2
  change Tendsto (fun n => ∫ w,Z n w ∂P) atTop (𝓝 (∫ w,(hM.moment ⊤).toLp _ w ∂P)) at hmean
  simp only [hz] at hmean
  exact tendsto_nhds_unique hmean tendsto_const_nhds

end Asakura.Chapter12
