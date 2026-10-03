import Chapter10TerminalIdentification
import Chapter10KyleOrderMoment

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter10
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The variance formula itself implies the L2 convergence at maturity;
this discharges the norm-limit input of the separate Fatou identification. -/
theorem kyle_error_L2_terminal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E : ℝ → Ω → ℝ) (S0 T : ℝ) (hT : 0<T)
    (hE : ∀ t∈Ioo 0 T,MemLp (E t) 2 P)
    (hvar : ∀ t∈Ioo 0 T,(∫ w,(E t w)^2 ∂P)=S0*(T-t)/T) :
    Tendsto (fun t => eLpNorm (E t) 2 P) (𝓝[<] T) (𝓝 0) := by
  have hn t (ht : t∈Ioo 0 T) : eLpNorm (E t) 2 P=ENNReal.ofReal (Real.sqrt (S0*(T-t)/T)) := by
    have hh := (hE t ht).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    norm_num only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] at hh
    rw [hvar t ht] at hh
    simpa only [Real.sqrt_eq_rpow,one_div] using hh
  have hc : Continuous (fun t : ℝ => ENNReal.ofReal (Real.sqrt (S0*(T-t)/T))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp ((continuous_const.mul (continuous_const.sub continuous_id)).div_const _))
  have hl : Tendsto (fun t : ℝ => ENNReal.ofReal (Real.sqrt (S0*(T-t)/T))) (𝓝[<] T) (𝓝 0) := by
    simpa using (hc.continuousAt (x := T)).tendsto.mono_left nhdsWithin_le_nhds
  apply hl.congr'
  rw [←nhdsWithin_Ioo_eq_nhdsLT hT]
  exact (show ∀ᶠ t in 𝓝[Ioo (0:ℝ) T] T,t∈Ioo 0 T from self_mem_nhdsWithin).mono
    (fun t ht => (hn t ht).symm)

end Asakura.Chapter10
