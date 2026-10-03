import FullAuditHeatKernel
import FullAuditCLTHessian

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.FullAudit

/-- Differentiation along the actual affine segment in the CLT proof. -/
theorem heatAverage_line_raw {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hdf : Continuous df)
    (C D : ℝ) (hf : ∀ x, ‖f x‖ ≤ C) (hb : ∀ x, ‖df x‖ ≤ D)
    (x t u v s : ℝ) (ht : 0 < t+s*v) :
    HasDerivAt (fun r => heatAverage f (x+r*u) (t+r*v))
      (∫ z, df (x+s*u+Real.sqrt (t+s*v)*z)*(u+v*z/(2*Real.sqrt (t+s*v))) ∂gaussianReal 0 1) s := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hD : 0 ≤ D := (norm_nonneg (df 0)).trans (hb 0)
  have hs : 0 < Real.sqrt ((t+s*v)/2) := Real.sqrt_pos.2 (by linarith)
  have hiZ : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num)
  let S : Set ℝ := {r | (t+s*v)/2 < t+r*v}
  have hS : S ∈ 𝓝 s :=
    (show Continuous (fun r : ℝ => t+r*v) by fun_prop).continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := S)
    (bound := fun z => D*(‖u‖+‖v‖*‖z‖/(2*Real.sqrt ((t+s*v)/2))))
    (F' := fun r z => df (x+r*u+Real.sqrt (t+r*v)*z)*(u+v*z/(2*Real.sqrt (t+r*v))))
    hS ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun r => (hfc.comp (by fun_prop)).aestronglyMeasurable
  · exact Integrable.of_bound (hfc.comp (by fun_prop)).aestronglyMeasurable C (ae_of_all _ fun z => hf _)
  · exact ((hdf.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · apply ae_of_all
    intro z r hr
    have hr0 : 0 < t+r*v := lt_trans (by linarith : 0 < (t+s*v)/2) hr
    have hden : ‖v*z/(2*Real.sqrt (t+r*v))‖ ≤ ‖v‖*‖z‖/(2*Real.sqrt ((t+s*v)/2)) := by
      rw [norm_div,norm_mul,Real.norm_eq_abs (2*Real.sqrt (t+r*v)),abs_of_pos (by positivity)]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr.le) (by norm_num))
    rw [norm_mul]
    exact mul_le_mul (hb _) ((norm_add_le _ _).trans (add_le_add le_rfl hden)) (norm_nonneg _) hD
  · exact ((integrable_const ‖u‖).add ((hiZ.norm.const_mul ‖v‖).div_const _)).const_mul D
  · apply ae_of_all
    intro z r hr
    have hr0 : 0 < t+r*v := lt_trans (by linarith : 0 < (t+s*v)/2) hr
    have htime := (((hasDerivAt_id r).mul_const v).const_add t).sqrt hr0.ne'
    have harg := (((hasDerivAt_id r).mul_const u).const_add x).add (htime.mul_const z)
    convert (hd (x+r*u+Real.sqrt (t+r*v)*z)).comp r harg using 1
    · rfl
    · simp only [mul_one,one_mul,id_eq]; ring

/-- The line derivative after the same Gaussian integration-by-parts step. -/
theorem heatAverage_line_derivative {f df ddf : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hdd : ∀ x, HasDerivAt df (ddf x) x)
    (hcdd : Continuous ddf) (C D E : ℝ)
    (hf : ∀ x, ‖f x‖ ≤ C) (hdf : ∀ x, ‖df x‖ ≤ D) (hddf : ∀ x, ‖ddf x‖ ≤ E)
    (x t u v s : ℝ) (ht : 0 < t+s*v) :
    HasDerivAt (fun r => heatAverage f (x+r*u) (t+r*v))
      (u*heatAverage df (x+s*u) (t+s*v)+(v/2)*heatAverage ddf (x+s*u) (t+s*v)) s := by
  have hcdf : Continuous df := continuous_iff_continuousAt.mpr fun x => (hdd x).continuousAt
  have hs := Real.sqrt_pos.2 ht
  have hcomp : ∀ z, HasDerivAt (fun z => df (x+s*u+Real.sqrt (t+s*v)*z))
      (Real.sqrt (t+s*v)*ddf (x+s*u+Real.sqrt (t+s*v)*z)) z := by
    intro z
    convert (hdd (x+s*u+Real.sqrt (t+s*v)*z)).comp z
      (((hasDerivAt_id z).const_mul (Real.sqrt (t+s*v))).const_add (x+s*u)) using 1
    · rfl
    · simp only [mul_one]; ring
  have hibp := gaussian_ibp_bounded (m := 0) (v := 1) (by norm_num)
    hcomp (by fun_prop) D (Real.sqrt (t+s*v)*E) (fun z => hdf _) (fun z => by
      rw [norm_mul,Real.norm_eq_abs,abs_of_pos hs]
      exact mul_le_mul_of_nonneg_left (hddf _) hs.le)
  simp only [NNReal.coe_one,sub_zero,div_one,integral_const_mul] at hibp
  have hi : Integrable (fun z => df (x+s*u+Real.sqrt (t+s*v)*z)) (gaussianReal 0 1) :=
    Integrable.of_bound (hcdf.comp (by fun_prop)).aestronglyMeasurable D (ae_of_all _ fun z => hdf _)
  have hiz : Integrable (fun z => z*df (x+s*u+Real.sqrt (t+s*v)*z)) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num)).mul_bdd
      (hcdf.comp (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun z => hdf _)
  have hraw := heatAverage_line_raw hd hcdf C D hf hdf x t u v s ht
  convert hraw using 1
  calc
    _ = u*(∫ z, df (x+s*u+Real.sqrt (t+s*v)*z) ∂gaussianReal 0 1) +
        (v/(2*Real.sqrt (t+s*v)))*(∫ z, z*df (x+s*u+Real.sqrt (t+s*v)*z) ∂gaussianReal 0 1) := by
      rw [← hibp]
      dsimp [heatAverage]
      field_simp
    _ = ∫ z, u*df (x+s*u+Real.sqrt (t+s*v)*z)+
        (v/(2*Real.sqrt (t+s*v)))*(z*df (x+s*u+Real.sqrt (t+s*v)*z)) ∂gaussianReal 0 1 := by
      rw [integral_add (hi.const_mul _) (hiz.const_mul _),integral_const_mul,integral_const_mul]
    _ = _ := integral_congr_ae (ae_of_all _ fun z => by ring)

/-- A test function together with its actual successive derivatives and bounds. -/
structure HeatTest where
  F : ℕ → ℝ → ℝ
  C : ℕ → ℝ
  continuous : ∀ n, Continuous (F n)
  derivative : ∀ n x, HasDerivAt (F n) (F (n+1) x) x
  bound : ∀ n x, ‖F n x‖ ≤ C n

theorem HeatTest.bound_nonneg (f : HeatTest) (n : ℕ) : 0 ≤ f.C n :=
  (norm_nonneg (f.F n 0)).trans (f.bound n 0)

/-- Interior differentiation remains valid when the segment ends at time zero;
if its entire time coordinate is zero, use the ordinary spatial derivative. -/
theorem HeatTest.segment_derivative (f : HeatTest) (k : ℕ) (x t u v s : ℝ)
    (hv : 0 ≤ v) (hvt : v ≤ t) (hs : s ∈ Ico (0:ℝ) 1) :
    HasDerivAt (fun r => heatAverage (f.F k) (x+r*u) (t-r*v))
      (u*heatAverage (f.F (k+1)) (x+s*u) (t-s*v)-
        (v/2)*heatAverage (f.F (k+2)) (x+s*u) (t-s*v)) s := by
  by_cases ht : t = 0
  · have hv0 : v = 0 := by linarith
    simp only [ht,hv0,mul_zero,sub_zero,heatAverage_zero,zero_div,zero_mul]
    convert (f.derivative k (x+s*u)).comp s (((hasDerivAt_id s).mul_const u).const_add x) using 1
    · rfl
    · simp only [one_mul]; ring
  · have hpos : 0 < t-s*v := by
      have ht0 : 0 < t := lt_of_le_of_ne (hv.trans hvt) (Ne.symm ht)
      nlinarith [mul_pos (sub_pos.mpr hs.2) ht0,mul_nonneg hs.1 (sub_nonneg.mpr hvt)]
    have hh := heatAverage_line_derivative (f.derivative k) (f.derivative (k+1))
      (f.continuous (k+2)) (f.C k) (f.C (k+1)) (f.C (k+2))
      (f.bound k) (f.bound (k+1)) (f.bound (k+2)) x t u (-v) s (by simpa using hpos)
    simpa only [mul_neg,neg_div,neg_mul,add_neg_cancel_right,sub_eq_add_neg] using hh

/-- Continuity of every derivative convolution along the closed segment. -/
theorem HeatTest.segment_continuous (f : HeatTest) (k : ℕ) (x t u v : ℝ) :
    Continuous (fun s => heatAverage (f.F k) (x+s*u) (t-s*v)) :=
  (heatAverage_continuous (f.continuous k) (f.C k) (f.bound k)).comp (show Continuous (fun s : ℝ => (x+s*u,t-s*v)) by fun_prop)

/-- The exact Taylor identity used for each triangular-array increment. -/
theorem HeatTest.taylor_increment (f : HeatTest) (x t u v : ℝ)
    (hv : 0 ≤ v) (hvt : v ≤ t) :
    heatAverage (f.F 0) (x+u) (t-v) = heatAverage (f.F 0) x t +
      u*heatAverage (f.F 1) x t - (v/2)*heatAverage (f.F 2) x t +
      (u^2/2)*heatAverage (f.F 2) x t +
      cltHessianRemainder
        (fun s => heatAverage (f.F 2) (x+s*u) (t-s*v))
        (fun s => (1/2)*heatAverage (f.F 3) (x+s*u) (t-s*v))
        (fun s => (1/4)*heatAverage (f.F 4) (x+s*u) (t-s*v)) u v := by
  let H := fun k s => heatAverage (f.F k) (x+s*u) (t-s*v)
  have hc : ∀ k, Continuous (H k) := fun k => f.segment_continuous k x t u v
  have hd : ∀ k s, s ∈ Ioo (0:ℝ) 1 → HasDerivAt (H k) (u*H (k+1) s-(v/2)*H (k+2) s) s :=
    fun k s hs => f.segment_derivative k x t u v s hv hvt ⟨hs.1.le,hs.2⟩
  have htay := clt_taylor_segment (H 0) (fun s => u*H 1 s-(v/2)*H 2 s)
    (fun s => u^2*H 2 s-u*v*H 3 s+(v^2/4)*H 4 s)
    (hc 0).continuousOn (by fun_prop) (by fun_prop) (hd 0) (by
      intro s hs
      convert ((hd 1 s hs).const_mul u).sub ((hd 2 s hs).const_mul (v/2)) using 1 <;> ring)
  have hi : ∀ k, IntervalIntegrable (fun s => H k s*(1-s)) volume 0 1 := by
    intro k
    apply Continuous.intervalIntegrable
    exact (hc k).mul (by fun_prop)
  have hconst : ∫ s in (0:ℝ)..1, H 2 0*(1-s) = H 2 0/2 := by
    rw [intervalIntegral.integral_const_mul,clt_weight_integrals.1]; ring
  have hsplit : (∫ s in (0:ℝ)..1, (u^2*H 2 s-u*v*H 3 s+(v^2/4)*H 4 s)*(1-s)) =
      u^2*(∫ s in (0:ℝ)..1, H 2 s*(1-s))-
        u*v*(∫ s in (0:ℝ)..1, H 3 s*(1-s))+
        (v^2/4)*(∫ s in (0:ℝ)..1, H 4 s*(1-s)) := by
    simp_rw [add_mul,sub_mul,mul_assoc]
    rw [intervalIntegral.integral_add ((hi 2).const_mul _ |>.sub (((hi 3).const_mul v).const_mul u)) ((hi 4).const_mul _),
      intervalIntegral.integral_sub ((hi 2).const_mul _) (((hi 3).const_mul v).const_mul u)]
    simp only [intervalIntegral.integral_const_mul]
  have hr : cltHessianRemainder (H 2) (fun s => (1/2)*H 3 s) (fun s => (1/4)*H 4 s) u v =
      u^2*((∫ s in (0:ℝ)..1,H 2 s*(1-s))-H 2 0/2) -
        u*v*(∫ s in (0:ℝ)..1,H 3 s*(1-s))+
        (v^2/4)*(∫ s in (0:ℝ)..1,H 4 s*(1-s)) := by
    unfold cltHessianRemainder
    simp_rw [sub_mul,mul_assoc]
    rw [intervalIntegral.integral_sub (hi 2) (by apply Continuous.intervalIntegrable; fun_prop),hconst]
    simp only [intervalIntegral.integral_const_mul]
    ring
  rw [hsplit] at htay
  have hgoal : H 0 1 = H 0 0+u*H 1 0-(v/2)*H 2 0+(u^2/2)*H 2 0+
      cltHessianRemainder (H 2) (fun s => (1/2)*H 3 s) (fun s => (1/4)*H 4 s) u v := by
    rw [hr]
    linarith
  simpa only [H,one_mul,zero_mul,add_zero,sub_zero] using hgoal

end Asakura.FullAudit
