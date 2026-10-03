import Chapter12AsianMomentTimeKernel

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

noncomputable def asianRemainingMoment (T : ℝ) (hT : 0≤T) (x σ r : ℝ) (j : ℕ)
    (f : C(Icc (0:ℝ) T,ℝ)) (s : Icc (0:ℝ) T) : ℝ :=
  ∫ t in s.val..T,t^j*(x*Real.exp ((r-σ^2/2)*t+σ*f (projIcc 0 T hT t)))

theorem asian_remaining_moment_measurable (T : ℝ) (hT : 0≤T) (x σ r : ℝ) (j : ℕ) :
    Measurable (fun z : C(Icc (0:ℝ) T,ℝ) × Icc (0:ℝ) T =>
      asianRemainingMoment T hT x σ r j z.1 z.2) := by
  let K := fun z : (C(Icc (0:ℝ) T,ℝ) × Icc (0:ℝ) T) × ℝ =>
    (Ioi z.1.2.val).indicator
      (fun t => t^j*(x*Real.exp ((r-σ^2/2)*t+σ*z.1.1 (projIcc 0 T hT t)))) z.2
  have hK : Measurable K := by
    have ha : Continuous (fun z : (C(Icc (0:ℝ) T,ℝ) × Icc (0:ℝ) T) × ℝ =>
      z.2^j*(x*Real.exp ((r-σ^2/2)*z.2+σ*z.1.1 (projIcc 0 T hT z.2)))) := by fun_prop
    exact ha.measurable.indicator (measurableSet_lt
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst)) measurable_snd)
  have hm := (hK.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0:ℝ) T))).measurable
  have he (z : C(Icc (0:ℝ) T,ℝ) × Icc (0:ℝ) T) :
      (∫ t,K (z,t) ∂volume.restrict (Ioc (0:ℝ) T))=asianRemainingMoment T hT x σ r j z.1 z.2 := by
    dsimp only [K,asianRemainingMoment]
    rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
      intervalIntegral.integral_of_le z.2.property.2]
    have hs : Ioi z.2.val ∩ Ioc (0:ℝ) T=Ioc z.2.val T := by
      ext t
      simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
      constructor
      · exact fun ht => ⟨ht.1,ht.2.2⟩
      · exact fun ht => ⟨ht.1,z.2.property.1.trans_lt ht.1,ht.2⟩
    rw [hs]
  simpa only [he] using hm

end Asakura.Chapter12
