import Chapter5PerturbationActualFamily
import Chapter5PointEnergyNorm

open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 9000000
set_option backward.isDefEq.respectTransparency false

/-- The time-uniform perturbation conclusion follows from the same
actual BSDE estimates, including the boundedness of the time supremum. -/
theorem perturbation_actual_uniform_time_bigO
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
    (sol : ℝ → BSDEFiniteEnergyData P F W c R)
    (base : BSDEFiniteEnergyData P F W c R)
    (iter : ℕ → ℝ → BSDEFiniteEnergyData P F W c R)
    (hiter0 : ∀ ε,iter 0 ε=base)
    (f₀ f₁ : (Ω × ℝ) × (ℝ × ℝ) → ℝ) (hfm₀ : Measurable f₀) (hfm₁ : Measurable f₁)
    (hf₀ : MemLp (fun z => f₀ (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hf₁ : MemLp (fun z => f₁ (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C₀ C₁ β ell mu ε₀ : ℝ) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (he₀ : 0<ε₀)
    (hell : 0<ell) (hmu : 0<mu) (hgap : C₀+ε₀*C₁<ell^2)
    (hβ : (C₀+ε₀*C₁)*(2+ell^2)+mu^2≤β)
    (hl₀ : ∀ z y₁ z₁ y₂ z₂,|f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂)|≤C₀*(|y₁-y₂|+|z₁-z₂|))
    (hl₁ : ∀ z y₁ z₁ y₂ z₂,|f₁ (z,y₁,z₁)-f₁ (z,y₂,z₂)|≤C₁*(|y₁-y₂|+|z₁-z₂|))
    (hsol : ∀ ε,|ε|≤ε₀ → ∀ w r,r∈Icc 0 R → (sol ε).B (w,r)=
      -(f₀ ((w,r),(sol ε).Y (realTimeClamp r) w,(sol ε).Z (w,r))+ε*f₁ ((w,r),(sol ε).Y (realTimeClamp r) w,(sol ε).Z (w,r))))
    (hbase : ∀ w r,r∈Icc 0 R → base.B (w,r)= -f₀ ((w,r),base.Y (realTimeClamp r) w,base.Z (w,r)))
    (hstep : ∀ n ε,|ε|≤ε₀ → ∀ w r,r∈Icc 0 R → (iter (n+1) ε).B (w,r)=
      -(f₀ ((w,r),(iter (n+1) ε).Y (realTimeClamp r) w,(iter (n+1) ε).Z (w,r))+
        ε*f₁ ((w,r),(iter n ε).Y (realTimeClamp r) w,(iter n ε).Z (w,r))))
    (hterm : ∀ n ε,|ε|≤ε₀ → (iter n ε).Y (realTimeClamp R) =ᵐ[P] (sol ε).Y (realTimeClamp R)) :
    ∀ n,(fun ε => ⨆ t : Icc (0:ℝ) R,pointEnergyNorm P
      (fun w => (iter n ε).Y (realTimeClamp t.val) w-(sol ε).Y (realTimeClamp t.val) w))
        =O[𝓝 0] (fun ε : ℝ => |ε|^(n+1)) := by
  letI : Nonempty (Icc (0:ℝ) R) := ⟨⟨0,le_rfl,hR⟩⟩
  let C := C₀+ε₀*C₁
  have hC : 0≤C := add_nonneg hC₀ (mul_nonneg he₀.le hC₁)
  have hC₀C : C₀≤C := le_add_of_nonneg_right (mul_nonneg he₀.le hC₁)
  have hβ0 : 0≤β := (add_nonneg (mul_nonneg hC (by positivity)) (sq_nonneg mu)).trans hβ
  have hl₀C z y₁ z₁ y₂ z₂ : |f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂)|≤C*(|y₁-y₂|+|z₁-z₂|) :=
    (hl₀ z y₁ z₁ y₂ z₂).trans (mul_le_mul_of_nonneg_right hC₀C (by positivity))
  have hfamily := perturbation_actual_family_bigO P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc hclock
    R hR hRT sol base iter hiter0 f₀ f₁ hfm₀ hfm₁ hf₀ hf₁ C₀ C₁ β ell mu ε₀ hC₀ hC₁ he₀ hell hmu hgap hβ hl₀ hl₁ hsol hbase hstep hterm
  have hsmall : ∀ᶠ ε : ℝ in 𝓝 0,|ε|≤ε₀ := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) he₀] with ε he
    exact (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using he : |ε|<ε₀).le
  intro n
  cases n with
  | zero =>
    let D := finiteEnergyNorm P R β (fun z => f₁ (z,base.Y (realTimeClamp z.2) z.1,base.Z z))
    apply nonnegative_sup_bigO _ (D/mu) ε₀ he₀ 1 (fun _ _ => pointEnergyNorm_nonneg _ _)
    intro ε he t
    have ht : (sol ε).Y (realTimeClamp R) =ᵐ[P] base.Y (realTimeClamp R) := by
      simpa only [hiter0] using (hterm 0 ε he).symm
    have hh := perturbation_base_actual_estimate P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc hclock
      R hR hRT (sol ε) base f₀ f₁ hfm₀ hfm₁ hf₀ hf₁ C₀ C₁ β (ell^2) (mu^2) ε ε₀ hC₀ hC₁ he
      hgap (sq_pos_of_pos hmu) hβ hl₀ hl₁ (hsol ε he) hbase ht
    have hpt := point_norm_from_weighted_estimate P (fun w => (sol ε).Y (realTimeClamp t.val) w-base.Y (realTimeClamp t.val) w)
      β t.val ε mu D hβ0 t.property.1 hmu (finiteEnergyNorm_nonneg _ _ _ _)
      (by simpa only [D,finiteEnergyNorm_sq P R β hR] using hh.1 t.val t.property)
    rw [pointEnergyNorm_sub_comm] at hpt
    rw [hiter0]
    convert hpt using 1 <;> ring
  | succ n =>
    let E := fun ε => finiteEnergyNorm P R β (fun z => (iter n ε).Y (realTimeClamp z.2) z.1-(sol ε).Y (realTimeClamp z.2) z.1)+
      finiteEnergyNorm P R β (fun z => (iter n ε).Z z-(sol ε).Z z)
    apply uniform_time_bound_bigO _ E (C₁/mu) (by positivity) (n+1)
      (fun _ _ => pointEnergyNorm_nonneg _ _) (fun _ => add_nonneg (finiteEnergyNorm_nonneg _ _ _ _) (finiteEnergyNorm_nonneg _ _ _ _))
    · filter_upwards [hsmall] with ε he
      intro t
      have hh := perturbation_iteration_actual_estimate P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc hclock
        R hR hRT (iter (n+1) ε) (iter n ε) (sol ε) f₀ f₁ hfm₀ hfm₁ hf₀ hf₁ C C₁ β (ell^2) (mu^2) ε hC hC₁
        hgap (sq_pos_of_pos hmu) hβ hl₀C hl₁ (hstep n ε he) (hsol ε he) (hterm (n+1) ε he)
      let D := finiteEnergyNorm P R β (fun z => f₁ (z,(iter n ε).Y (realTimeClamp z.2) z.1,(iter n ε).Z z)-f₁ (z,(sol ε).Y (realTimeClamp z.2) z.1,(sol ε).Z z))
      have hpt := point_norm_from_weighted_estimate P (fun w => (iter (n+1) ε).Y (realTimeClamp t.val) w-(sol ε).Y (realTimeClamp t.val) w)
        β t.val ε mu D hβ0 t.property.1 hmu (finiteEnergyNorm_nonneg _ _ _ _)
        (by simpa only [D,finiteEnergyNorm_sq P R β hR] using hh.1 t.val t.property)
      have hd : D≤C₁*E ε := bsde_generator_difference_norm P F W c R β hR hβ0 (iter n ε) (sol ε) f₁ hfm₁ hf₁ C₁ hC₁ hl₁
      calc
        _ ≤ |ε|/mu*D := hpt
        _ ≤ |ε|/mu*(C₁*E ε) := mul_le_mul_of_nonneg_left hd (by positivity)
        _ = _ := by ring
    · exact (hfamily n).1.add (hfamily n).2

end Asakura.Chapter5
