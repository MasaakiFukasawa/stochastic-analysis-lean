import Chapter5TwoBSDEApriori
import Chapter5PerturbationNormCoefficients

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- Actual two-solution perturbation estimate. Equal terminal conditions
and the discrepancy epsilon G are substituted into the weighted Ito
estimate; the factor epsilon squared is derived inside the integrals. -/
theorem bsde_perturbation_energy_constructed
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
    (f : (Ω × ℝ) × (ℝ × ℝ) → ℝ) (hfm : Measurable f)
    (hf0 : MemLp (fun z => f (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C β ell mu2 : ℝ) (hC : 0≤C) (hell : C<ell) (hmu2 : 0<mu2) (hβ : C*(2+ell)+mu2≤β)
    (hl : ∀ z y₁ z₁ y₂ z₂,|f (z,y₁,z₁)-f (z,y₂,z₂)|≤C*(|y₁-y₂|+|z₁-z₂|))
    (hBu : ∀ w r,r∈Icc 0 R → u.B (w,r)= -f ((w,r),u.Y (realTimeClamp r) w,u.Z (w,r)))
    (ε : ℝ) (G : Ω × ℝ → ℝ)
    (hterm : u.Y (realTimeClamp R) =ᵐ[P] v.Y (realTimeClamp R))
    (hdis : ∀ w r,r∈Icc 0 R → f ((w,r),v.Y (realTimeClamp r) w,v.Z (w,r))+v.B (w,r)=ε*G (w,r)) :
    let K := ε^2*(∫ w,(∫ r in 0..R,Real.exp (β*r)*G (w,r)^2) ∂P)/mu2
    (∀ t∈Icc 0 R,(∫ w,Real.exp (β*t)*(u.Y (realTimeClamp t) w-v.Y (realTimeClamp t) w)^2 ∂P)≤K) ∧
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*(u.Y (realTimeClamp r) w-v.Y (realTimeClamp r) w)^2) ∂P)≤R*K ∧
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*(u.Z (w,r)-v.Z (w,r))^2) ∂P)≤ell/(ell-C)*K := by
  dsimp only
  have ht : (∫ w,Real.exp (β*R)*(u.Y (realTimeClamp R) w-v.Y (realTimeClamp R) w)^2 ∂P)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hterm] with w hw
    simp only [hw,sub_self,zero_pow (by decide : 2≠0),mul_zero,Pi.zero_apply]
  have he : (∫ w,(∫ r in 0..R,Real.exp (β*r)*
      (f ((w,r),v.Y (realTimeClamp r) w,v.Z (w,r))+v.B (w,r))^2) ∂P)=
      ε^2*(∫ w,(∫ r in 0..R,Real.exp (β*r)*G (w,r)^2) ∂P) := by
    calc
      _ = ∫ w,(∫ r in 0..R,ε^2*(Real.exp (β*r)*G (w,r)^2)) ∂P := by
        apply integral_congr_ae
        exact ae_of_all _ fun w => intervalIntegral.integral_congr fun r hr => by
          rw [hdis w r (by simpa only [uIcc_of_le hR] using hr)]
          ring
      _ = _ := by simp_rw [intervalIntegral.integral_const_mul,integral_const_mul]
  have hh := two_bsde_apriori_constructed P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc hclock
    R hR hRT u v f hfm hf0 C β ell mu2 hC hell hmu2 hβ hl hBu
  dsimp only at hh
  simpa only [ht,he,zero_add] using hh

end Asakura.Chapter5
