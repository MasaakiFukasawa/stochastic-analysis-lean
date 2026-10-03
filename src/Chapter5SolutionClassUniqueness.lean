import Chapter5FrozenClassRelation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Every solution with the actual nonlinear drift gives a fixed point
of the concrete relation. Its uniqueness is therefore uniqueness of
both process classes, not just of a selected construction. -/
theorem nonlinear_solution_class_uniqueness
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (W : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ) (hco : ∀ r,∃ j,r≤c j)
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β) (ξ : Ω → ℝ)
    (f : (Ω × ℝ) × (ℝ × ℝ) → ℝ)
    (hunique : ∃! x,frozenBSDEClassRelation P F W c hco R β hR hβ ξ f x x)
    (u v : BSDEFiniteEnergyData P F W c R)
    (hup : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => u.Y (realTimeClamp z.2.val) z.1))
    (hvp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => v.Y (realTimeClamp z.2.val) z.1))
    (hut : u.Y (realTimeClamp R) =ᵐ[P] ξ) (hvt : v.Y (realTimeClamp R) =ᵐ[P] ξ)
    (huB : ∀ w r,r∈Icc 0 R → u.B (w,r)= -f ((w,r),u.Y (realTimeClamp r) w,u.Z (w,r)))
    (hvB : ∀ w r,r∈Icc 0 R → v.B (w,r)= -f ((w,r),v.Y (realTimeClamp r) w,v.Z (w,r))) :
    ((fun z : Ω × ℝ => u.Y (realTimeClamp z.2) z.1) =ᵐ[P.prod (volume.restrict (Ioc 0 R))]
      fun z => v.Y (realTimeClamp z.2) z.1) ∧
    (u.Z =ᵐ[P.prod (volume.restrict (Ioc 0 R))] v.Z) := by
  let iu := u.outputY P F W c R hup
  let ju := u.outputZ P F W c hco R
  let iv := v.outputY P F W c R hvp
  let jv := v.outputZ P F W c hco R
  let xu := WithLp.toLp 2 (iu.realize P F R β hR hβ,ju.realize P F R β hR hβ)
  let xv := WithLp.toLp 2 (iv.realize P F R β hR hβ,jv.realize P F R β hR hβ)
  have hu : frozenBSDEClassRelation P F W c hco R β hR hβ ξ f xu xu :=
    ⟨iu,ju,rfl,rfl,u,hup,hut,huB,rfl,rfl⟩
  have hv : frozenBSDEClassRelation P F W c hco R β hR hβ ξ f xv xv :=
    ⟨iv,jv,rfl,rfl,v,hvp,hvt,hvB,rfl,rfl⟩
  obtain ⟨x,hx,huniq⟩ := hunique
  have he : xu=xv := (huniq xu hu).trans (huniq xv hv).symm
  have hey : iu.realize P F R β hR hβ=iv.realize P F R β hR hβ := congrArg WithLp.fst he
  have hez : ju.realize P F R β hR hβ=jv.realize P F R β hR hβ := congrArg WithLp.snd he
  exact ⟨(iu.realize_eq_iff P F R β hR hβ iv).mp hey,(ju.realize_eq_iff P F R β hR hβ jv).mp hez⟩

end Asakura.Chapter5
