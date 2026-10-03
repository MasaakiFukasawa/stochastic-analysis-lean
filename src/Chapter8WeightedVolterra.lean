import Chapter8SmallMassBounds
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Compact

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Exponential weights make a Volterra map contractive on every finite
horizon. This is the deterministic construction used for variational ODEs. -/
theorem weighted_volterra_lipschitz {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 ≤ T) (K : ℝ≥0) (a : ℝ) (ha : 0<a)
    (F : ℝ → E → E) (hFc : Continuous (Function.uncurry F))
    (hF : ∀ t,LipschitzWith K (F t))
    (q : ℝ → E) (P : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E))
    (hP : ∀ z t,P z t=Real.exp (-a*t.val) • (q t.val+
      ∫ s in 0..t.val,F s (Real.exp (a*s) • z (projIcc 0 T hT s)))) :
    ∀ z y,‖P z-P y‖ ≤ ((K:ℝ)/a)*‖z-y‖ := by
  intro z y
  have hcz : Continuous (fun s => F s (Real.exp (a*s) • z (projIcc 0 T hT s))) := by
    simpa only [Function.comp_def,Function.uncurry_def,Pi.smul_apply,Pi.smul_apply',id_eq] using hFc.comp (continuous_id.prodMk ((by fun_prop : Continuous (fun s : ℝ => Real.exp (a*s))).smul
      (z.continuous.comp continuous_projIcc)))
  have hcy : Continuous (fun s => F s (Real.exp (a*s) • y (projIcc 0 T hT s))) := by
    simpa only [Function.comp_def,Function.uncurry_def,Pi.smul_apply,Pi.smul_apply',id_eq] using hFc.comp (continuous_id.prodMk ((by fun_prop : Continuous (fun s : ℝ => Real.exp (a*s))).smul
      (y.continuous.comp continuous_projIcc)))
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖P z t-P y t‖ ≤ _
  have he : P z t-P y t=∫ s in 0..t.val,Real.exp (-a*t.val) •
      (F s (Real.exp (a*s) • z (projIcc 0 T hT s))-F s (Real.exp (a*s) • y (projIcc 0 T hT s))) := by
    rw [hP z t,hP y t,intervalIntegral.integral_smul,
      intervalIntegral.integral_sub (hcz.intervalIntegrable 0 t.val) (hcy.intervalIntegrable 0 t.val),← smul_sub]
    congr 1
    abel
  rw [he]
  have hbound s : ‖Real.exp (-a*t.val) •
      (F s (Real.exp (a*s) • z (projIcc 0 T hT s))-F s (Real.exp (a*s) • y (projIcc 0 T hT s)))‖ ≤
      (K:ℝ)*‖z-y‖*Real.exp (-a*(t.val-s)) := by
    have hn := (hF s).norm_sub_le (Real.exp (a*s) • z (projIcc 0 T hT s))
      (Real.exp (a*s) • y (projIcc 0 T hT s))
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hn
    have hz : ‖z (projIcc 0 T hT s)-y (projIcc 0 T hT s)‖ ≤ ‖z-y‖ :=
      (z-y).norm_coe_le_norm _
    have hh := hn.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le) K.coe_nonneg)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-a*t.val)).le
    have hee : Real.exp (-a*t.val)*Real.exp (a*s)=Real.exp (-a*(t.val-s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    convert hh' using 1
    rw [show Real.exp (-a*t.val)*((K:ℝ)*(Real.exp (a*s)*‖z-y‖))=
      (K:ℝ)*‖z-y‖*(Real.exp (-a*t.val)*Real.exp (a*s)) by ring,hee]
  have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) t.property.1
    (f := fun s => Real.exp (-a*t.val) • (F s (Real.exp (a*s) • z (projIcc 0 T hT s))-
      F s (Real.exp (a*s) • y (projIcc 0 T hT s))))
    (g := fun s => (K:ℝ)*‖z-y‖*Real.exp (-a*(t.val-s)))
    (ae_of_all _ (fun s _ => hbound s))
    ((by fun_prop : Continuous (fun s : ℝ => (K:ℝ)*‖z-y‖*Real.exp (-a*(t.val-s)))).intervalIntegrable 0 t.val)
  rw [intervalIntegral.integral_const_mul] at hh
  have hk := (small_mass_kernel_bound a 1 t.val ha (by norm_num) t.property.1).2
  simp only [div_one] at hk
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ (K:ℝ)*‖z-y‖))
  convert hh' using 1 <;> ring

end Asakura.Chapter8
