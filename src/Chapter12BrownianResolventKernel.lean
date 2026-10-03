import Chapter12ClampedPrefixKernel

open MeasureTheory Set
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem finite_terminal_kernel_raw (T:ℝ) :
    (finiteTimeIntervalVector T 0 T:ℝ → ℝ)=ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)] (fun _ => (1:ℝ)) := by
  have hp:(finiteTimeIntervalVector T 0 T:ℝ → ℝ)=ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
      (Ioc (0:ℝ) T).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  filter_upwards [hp,ae_restrict_mem (μ:=volume.restrict (Ioi (0:ℝ))) measurableSet_Iic,
    ae_restrict_of_ae (s:=Iic T) (ae_restrict_mem (μ:=volume) measurableSet_Ioi)] with s hs hT h0
  rw [hs,indicator_of_mem (show s∈Ioc (0:ℝ) T from ⟨h0,hT⟩)]

theorem brownian_resolvent_kernel {d:ℕ} (T:ℝ) (hT:0≤T)
    (c:Fin (d+1) → ℝ) (a:Fin (d+1) → ℝ → ℝ) (ha:∀j,Continuous (a j))
    (U:FiniteWienerHilbert d T)
    (hU:U=(∑j,c j • brownianTimeDirection (j,⟨T,hT,le_rfl⟩))+
      ∫s in 0..T,∑j,a j s • brownianTimeDirection (j,projIcc 0 T hT s))
    (i:Fin (d+1)) :
    (brownianCoordinateProjection T i U:ℝ → ℝ)=ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
      (fun r => c i+∫s in r..T,a i s) := by
  have he:brownianCoordinateProjection T i U=c i • finiteTimeIntervalVector T 0 T+
      ∫s in 0..T,a i s • finiteTimeIntervalVector T 0 (projIcc 0 T hT s).val := by
    rw [hU,map_add,brownian_coordinate_weighted_prefix,brownian_integral_prefix_coordinate T hT a ha i]
  rw [he]
  filter_upwards [Lp.coeFn_add (c i • finiteTimeIntervalVector T 0 T)
      (∫s in 0..T,a i s • finiteTimeIntervalVector T 0 (projIcc 0 T hT s).val),
    Lp.coeFn_smul (c i) (finiteTimeIntervalVector T 0 T),finite_terminal_kernel_raw T,
    clamped_prefix_L2_kernel T hT (a i) (ha i)] with r hadd hsm hterm hint
  rw [hadd,Pi.add_apply,hsm,Pi.smul_apply,hterm,hint,smul_eq_mul,mul_one]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_resolvent_kernel
