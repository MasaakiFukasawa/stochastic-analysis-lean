import Chapter5FrozenClassRelation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 7000000
set_option backward.isDefEq.respectTransparency false

/-- The chapter's actual frozen BSDE relation has exactly one fixed
point in the complete progressive weighted L² product space. Neither
existence of frozen solutions nor the contraction estimate is assumed. -/
theorem nonlinear_bsde_fixed_point_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (W A : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0<c j) (hcm : StrictMono c) (hcT : ∀ j,(c j:EReal)<T)
    (hct : StrictMono (fun j => realTimeClamp (T := T) (c j)))
    (hcut : ∀ j,realTimeClamp (T := T) (c j)<⊤)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (hco : ∀ r,∃ j,r≤c j)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hFnat : F (realTimeClamp R)=Asakura.nullAugmentation (m := m) P (pastSigma W (realTimeClamp R)))
    (ξ : Ω → ℝ) (hξ : MemLp ξ 2 P) (hξm : Measurable[F (realTimeClamp R)] ξ)
    (f : (Ω × ℝ) × (ℝ × ℝ) → ℝ) (hfm : Measurable f)
    (hfp : ∀ t : Icc (0:ℝ) R,
      @Measurable _ _ ((F (realTimeClamp t.val)).prod inferInstance) inferInstance
        (fun p : Ω × (Iic t × (ℝ × ℝ)) => f ((p.1,p.2.1.val.val),p.2.2)))
    (hf0 : MemLp (fun z => f (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C β : ℝ) (hC : 0≤C) (hb : 2*(1+R)*C^2<β)
    (hl : ∀ z y₁ z₁ y₂ z₂,|f (z,y₁,z₁)-f (z,y₂,z₂)|≤C*(|y₁-y₂|+|z₁-z₂|)) :
    ∃! x,frozenBSDEClassRelation P F W c hco R β hR (by nlinarith [sq_nonneg C]) ξ f x x := by
  have hβ : 0<β := lt_of_le_of_lt (by positivity) hb
  let μ := exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β
  let H := progressiveEnergyRange F (fun _ => R) μ
  let E := WithLp 2 (H × H)
  let rel := frozenBSDEClassRelation P F W c hco R β hR hβ.le ξ f
  letI : CompleteSpace H := weighted_progressive_complete F (fun _ => R) _ β
  have hex : ∀ x : E,∃ y,rel x y := by
    intro x
    obtain ⟨i,hi⟩ := finite_progressive_realize_surjective P F R β hR hβ.le x.fst
    obtain ⟨j,hj⟩ := finite_progressive_realize_surjective P F R β hR hβ.le x.snd
    let G := fun z => f (z,i.value z,j.value z)
    have hGm : Measurable G := hfm.comp (measurable_id.prodMk (i.measurable.prodMk j.measurable))
    have hGp := generator_progressive_substitution R (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))
      (fun w r y z => f ((w,r),y,z)) hfp i.value j.value i.progressive j.progressive
    have hG2 := generator_memLp _ f hfm i.value j.value i.measurable j.measurable i.energy j.energy hf0 C hC
      (fun z y z' => by simpa only [sub_zero] using hl z y z' 0 0)
    obtain ⟨u,hut,huB,hup⟩ := frozen_finite_energy_data_constructed P hT F hF hle hnull W A hW hA hclock
      c hc hcm hcT hct hcut hcc hco R hR hRT hFnat ξ hξ hξm G hGm hGp hG2
    let y : E := WithLp.toLp 2 ((u.outputY P F W c R hup).realize P F R β hR hβ.le,
      (u.outputZ P F W c hco R).realize P F R β hR hβ.le)
    exact ⟨y,i,j,hi,hj,u,hup,hut,huB,rfl,rfl⟩
  obtain ⟨hq,hq1⟩ := contraction_ratio R C β hR hb
  apply relational_fixed_point_from_squared_estimate rel hex (2*(1+R)*C^2/β) hq hq1
  intro x x' y y' hy hy'
  obtain ⟨i,j,hi,hj,u,hup,hut,huB,huy,huz⟩ := hy
  obtain ⟨i',j',hi',hj',v,hvp,hvt,hvB,hvy,hvz⟩ := hy'
  let G := fun z => f (z,i.value z,j.value z)
  let G' := fun z => f (z,i'.value z,j'.value z)
  let D := ∫ w,(∫ r in 0..R,Real.exp (β*r)*(G (w,r)-G' (w,r))^2) ∂P
  have hGm : Measurable G := hfm.comp (measurable_id.prodMk (i.measurable.prodMk j.measurable))
  have hG2 := generator_memLp _ f hfm i.value j.value i.measurable j.measurable i.energy j.energy hf0 C hC
    (fun z y z' => by simpa only [sub_zero] using hl z y z' 0 0)
  have hterm : u.Y (realTimeClamp R) =ᵐ[P] v.Y (realTimeClamp R) := hut.trans hvt.symm
  obtain ⟨hY,hZ⟩ := frozen_difference_apriori P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc
    (fun n w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))
    R hR hRT u v G G' hGm hG2 huB hvB hterm β hβ
  have hYn : ‖y.fst-y'.fst‖^2≤(R/β)*D := by
    rw [← huy,← hvy,(u.outputY P F W c R hup).difference_norm P F R β hR hβ.le (v.outputY P F W c R hvp)]
    exact hY
  have hZn : ‖y.snd-y'.snd‖^2≤(1/β)*D := by
    rw [← huz,← hvz,(u.outputZ P F W c hco R).difference_norm P F R β hR hβ.le (v.outputZ P F W c hco R)]
    exact hZ
  have hD : D≤2*C^2*(‖x.fst-x'.fst‖^2+‖x.snd-x'.snd‖^2) := by
    rw [← hi,← hi',← hj,← hj']
    exact weighted_generator_difference_energy P F R β hR hβ.le i j i' j' f hfm hf0 C hC hl
  simp only [dist_eq_norm,WithLp.prod_norm_sq_eq_of_L2,WithLp.sub_fst,WithLp.sub_snd]
  calc
    _ ≤ (R/β)*D+(1/β)*D := add_le_add hYn hZn
    _ = ((1+R)/β)*D := by ring
    _ ≤ ((1+R)/β)*(2*C^2*(‖x.fst-x'.fst‖^2+‖x.snd-x'.snd‖^2)) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by ring

end Asakura.Chapter5
