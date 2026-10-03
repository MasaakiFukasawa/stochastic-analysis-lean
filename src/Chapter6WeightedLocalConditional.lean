import Chapter6FiniteRealConditional
import Chapter5ProgressiveDriftVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The compensated weighted solution is a genuine martingale, using
only the integrable path bound obtained after changing measure. -/
theorem weighted_local_conditional {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (Y A N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (hYa : ∀ t,t<⊤ → Measurable[F t] (Y t)) (hAa : ∀ t,t<⊤ → Measurable[F t] (A t))
    (hYc : ∀ w t,t<⊤ → ContinuousAt (fun s => Y s w) t)
    (hAc : ∀ w,Continuous (fun t => A t w))
    (φ : ℝ → Ω → ℝ) (hφc : ∀ w,Continuous (fun r => φ r w))
    (R : ℝ) (hR : 0≤R) (hφa : ∀ r∈Icc 0 R,Measurable[F (realTimeClamp r)] (φ r))
    (L K : ℝ) (hL : 0≤L) (hK : 0≤K)
    (hAb : ∀ w r,r∈Icc 0 R → |A (realTimeClamp r) w|≤L)
    (hφb : ∀ w r,r∈Icc 0 R → |φ r w|≤K)
    (U : Ω → ℝ) (hU : Integrable U P)
    (hYb : ∀ᵐ w ∂P,∀ r∈Icc 0 R,|Y (realTimeClamp r) w|≤U w)
    (he : ∀ r∈Icc 0 R,(fun w => Y (realTimeClamp r) w*A (realTimeClamp r) w+∫ s in 0..r,A (realTimeClamp s) w*φ s w)=ᵐ[P]
      fun w => Y ⊥ w*A ⊥ w+N (realTimeClamp r) w)
    (s : ℝ) (hs : s∈Icc 0 R) :
    Integrable (fun w => Y (realTimeClamp R) w*A (realTimeClamp R) w+∫ r in s..R,A (realTimeClamp r) w*φ r w) P ∧
    P[(fun w => Y (realTimeClamp R) w*A (realTimeClamp R) w+∫ r in s..R,A (realTimeClamp r) w*φ r w)|F (realTimeClamp s)]=ᵐ[P]
      fun w => Y (realTimeClamp s) w*A (realTimeClamp s) w := by
  have hT : (0:EReal)<⊤ := by simp
  let G := fun z : Ω × ℝ => A (realTimeClamp z.2) z.1*φ z.2 z.1
  have hGc w : Continuous (fun r => G (w,r)) := ((hAc w).comp real_time_clamp_continuous).mul (hφc w)
  have hGp := continuous_adapted_real_progressive F hF G R hR
    (fun r hr => (hAa _ (changed_time_finite r hr.1)).mul (hφa r hr)) (fun w => (hGc w).continuousOn)
  obtain ⟨C,hC,hCc,hCe⟩ := progressive_integrable_drift_variation hT F hF R hR le_top G hGp
    (fun w => ((hGc w).intervalIntegrable 0 R).1)
  have hCr r (hr : r∈Icc 0 R) w : C (realTimeClamp r) w=∫ u in 0..r,G (w,u) := by
    rw [hCe,finite_prefix_time_of_real R r hR hr le_top]
  have hz0 : realTimeClamp 0=(⊥ : HalfClosedTime) := by apply Subtype.ext; simp [realTimeClamp]
  have hC0 w : C ⊥ w=0 := by simpa only [hz0,intervalIntegral.integral_same] using hCr 0 ⟨le_rfl,hR⟩ w
  have hCb w r (hr : r∈Icc 0 R) : |C (realTimeClamp r) w|≤L*K*R := by
    rw [hCr r hr]
    have hb : ∀ u∈uIoc 0 r,‖G (w,u)‖≤L*K := by
      intro u hu
      have hu' : u∈Icc 0 R := by
        rw [uIoc_of_le hr.1] at hu
        exact ⟨hu.1.le,hu.2.trans hr.2⟩
      change ‖A (realTimeClamp u) w*φ u w‖≤L*K
      simp only [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul (hAb w u hu') (hφb w u hu') (abs_nonneg _) hL
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
    simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg hr.1] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hr.2 (mul_nonneg hL hK))
  let X := fun t w => Y t w*A t w+C t w
  have hXa t (ht : t<⊤) : Measurable[F t] (X t) := (hYa t ht |>.mul (hAa t ht)).add (hC.adapted t ht)
  have hXc w t (ht : t<⊤) : ContinuousAt (fun u => X u w) t :=
    ((hYc w t ht).mul (hAc w).continuousAt).add (hCc w).continuousAt
  have hXb : ∀ᵐ w ∂P,∀ r∈Icc 0 R,|X (realTimeClamp r) w|≤L*U w+L*K*R := by
    filter_upwards [hYb] with w hw
    intro r hr
    have hup : 0≤U w := (abs_nonneg _).trans (hw r hr)
    exact (abs_add_le _ _).trans (add_le_add (by
      rw [abs_mul]
      exact (mul_le_mul (hw r hr) (hAb w r hr) (abs_nonneg _) hup).trans_eq (mul_comm _ _)) (hCb w r hr))
  have hXe r (hr : r∈Icc 0 R) : X (realTimeClamp r)=ᵐ[P] fun w => X ⊥ w+N (realTimeClamp r) w := by
    filter_upwards [he r hr] with w hw
    dsimp [X]
    rw [hCr r hr,hC0,add_zero]
    exact hw
  have hmart := finite_real_local_conditional P F hF hle X N hN hXa hXc R hR
    (fun w => L*U w+L*K*R) ((hU.const_mul L).add (integrable_const _)) hXb hXe s hs
  have hXi : Integrable (X (realTimeClamp R)) P :=
    ((hU.const_mul L).add (integrable_const (L*K*R))).mono'
      (((hXa _ (changed_time_finite R hR)).mono (hle _) le_rfl).aestronglyMeasurable)
      (hXb.mono (fun w hw => by simpa only [Real.norm_eq_abs,Pi.add_apply] using hw R ⟨hR,le_rfl⟩))
  have hCi : Integrable (C (realTimeClamp s)) P :=
    (integrable_const (L*K*R)).mono'
      (((hC.adapted _ (changed_time_finite s hs.1)).mono (hle _) le_rfl).aestronglyMeasurable)
      (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using hCb w s hs))
  have hsub := condExp_sub hXi hCi (F (realTimeClamp s))
  have hfix := condExp_of_stronglyMeasurable (hle _) (hC.adapted _ (changed_time_finite s hs.1)).stronglyMeasurable hCi
  have heq : (fun w => Y (realTimeClamp R) w*A (realTimeClamp R) w+∫ r in s..R,A (realTimeClamp r) w*φ r w)=
      (fun w => X (realTimeClamp R) w-C (realTimeClamp s) w) := by
    funext w
    dsimp [X]
    rw [hCr R ⟨hR,le_rfl⟩,hCr s hs]
    have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume) ((hGc w).intervalIntegrable 0 s) ((hGc w).intervalIntegrable s R)
    change _+ (∫ r in s..R,G (w,r))= _
    linarith
  rw [heq]
  refine ⟨hXi.sub hCi,?_⟩
  filter_upwards [hsub,hmart] with w hw hm
  change P[(fun w => X (realTimeClamp R) w-C (realTimeClamp s) w)|F (realTimeClamp s)] w=_ at hw ⊢
  rw [hw,hfix]
  simp only [Pi.sub_apply]
  rw [hm]
  dsimp [X]
  ring

end Asakura.Chapter6
