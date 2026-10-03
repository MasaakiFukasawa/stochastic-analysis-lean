import Chapter9CompactParameterDerivative
import Chapter9SliceDerivatives

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Compact support provides a finite measure for differentiating the
ordinary Lebesgue integral; no global domination hypothesis is added. -/
theorem compact_support_integral_derivative {d : ℕ}
    (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (F D : ℝ → (Fin d → ℝ) → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hF : ContinuousOn F.uncurry (U ×ˢ univ)) (hcD : ContinuousOn D.uncurry (U ×ˢ univ))
    (hD : ∀ t∈U,∀ x,HasDerivAt (fun s => F s x) (D t x) t)
    (hF0 : ∀ t x,x∉K → F t x=0) (hD0 : ∀ t x,x∉K → D t x=0)
    (t : ℝ) (ht : t∈U) :
    HasDerivAt (fun s => ∫ x,F s x) (∫ x,D t x) t := by
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  have hd := compact_parameter_integral_derivative (volume.restrict K) K hK
    (ae_restrict_mem hK.measurableSet) F D U hU hF hcD hD t ht
  have he (s : ℝ) : (∫ x in K,F s x)=(∫ x,F s x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hF0 s)
  have heD : (∫ x in K,D t x)=(∫ x,D t x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hD0 t)
  simpa only [he,heD] using hd

/-- Joint smoothness supplies the continuity of the parameter derivative. -/
theorem compact_smooth_integral_derivative {d : ℕ}
    (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (F D : ℝ → (Fin d → ℝ) → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F.uncurry (U ×ˢ univ))
    (hD : ∀ t∈U,∀ x,HasDerivAt (fun s => F s x) (D t x) t)
    (hF0 : ∀ t x,x∉K → F t x=0) (hD0 : ∀ t x,x∉K → D t x=0)
    (t : ℝ) (ht : t∈U) :
    HasDerivAt (fun s => ∫ x,F s x) (∫ x,D t x) t := by
  have hc : ContinuousOn (fun z => fderiv ℝ F.uncurry z (1,0)) (U ×ˢ univ) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) (by simp)).clm_apply continuousOn_const
  have he (z : ℝ × (Fin d → ℝ)) (hz : z∈U ×ˢ univ) :
      fderiv ℝ F.uncurry z (1,0)=D z.1 z.2 := by
    have hd := time_slice_derivative F.uncurry z.1 z.2
      (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz))
    simpa only [iteratedFDeriv_one_apply] using hd.unique (hD z.1 hz.1 z.2)
  exact compact_support_integral_derivative K hK F D U hU hF.continuousOn
    (hc.congr (fun z hz => (he z hz).symm)) hD hF0 hD0 t ht
end Asakura.Chapter9
