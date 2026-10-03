import Chapter5TwoBSDEApriori

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- For two frozen solutions, the actual Ito a-priori theorem gives the
contraction constants T/beta and 1/beta. Equal terminal values remove
the terminal contribution. -/
theorem frozen_difference_apriori
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hA : LocalCovarianceWitness P F W W A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (u v : BSDEFiniteEnergyData P F W c R)
    (G H : Ω × ℝ → ℝ) (hGm : Measurable G)
    (hG2 : MemLp G 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hBu : ∀ w r,r∈Icc 0 R → u.B (w,r)= -G (w,r))
    (hBv : ∀ w r,r∈Icc 0 R → v.B (w,r)= -H (w,r))
    (hterminal : u.Y (realTimeClamp R) =ᵐ[P] v.Y (realTimeClamp R))
    (β : ℝ) (hβ : 0<β) :
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*(u.Y (realTimeClamp r) w-v.Y (realTimeClamp r) w)^2) ∂P)≤
      (R/β)*(∫ w,(∫ r in 0..R,Real.exp (β*r)*(G (w,r)-H (w,r))^2) ∂P) ∧
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*(u.Z (w,r)-v.Z (w,r))^2) ∂P)≤
      (1/β)*(∫ w,(∫ r in 0..R,Real.exp (β*r)*(G (w,r)-H (w,r))^2) ∂P) := by
  have hzero : (∫ w,Real.exp (β*R)*(u.Y (realTimeClamp R) w-v.Y (realTimeClamp R) w)^2 ∂P)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hterminal] with w hw
    simp only [hw,sub_self,zero_pow (by decide : 2≠0),mul_zero,Pi.zero_apply]
  have he : (∫ w,(∫ r in 0..R,Real.exp (β*r)*(G (w,r)+v.B (w,r))^2) ∂P)=
      ∫ w,(∫ r in 0..R,Real.exp (β*r)*(G (w,r)-H (w,r))^2) ∂P := by
    apply integral_congr_ae
    exact ae_of_all _ fun w => intervalIntegral.integral_congr fun r hr => by
      have hr' : r∈Icc 0 R := by simpa only [uIcc_of_le hR] using hr
      rw [hBv w r hr',sub_eq_add_neg]
  have hh := two_bsde_apriori_constructed P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc
    hclock R hR hRT u v (fun p => G p.1) (hGm.comp measurable_fst) hG2 0 β 1 β
    le_rfl (by norm_num) hβ (by simp) (by intros; simp) hBu
  dsimp only at hh
  simp only [hzero,he,zero_add,sub_zero,div_self (by norm_num : (1:ℝ)≠0),one_mul] at hh
  constructor
  · calc
      _ ≤ R*((∫ w,(∫ r in 0..R,Real.exp (β*r)*(G (w,r)-H (w,r))^2) ∂P)/β) := hh.2.1
      _ = _ := by ring
  · simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hh.2.2

end Asakura.Chapter5
