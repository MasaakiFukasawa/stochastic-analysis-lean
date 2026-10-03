import Chapter11AffineDriver
import Chapter11LocalC12Stopped
import Chapter11IntervalExit

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 5200000
set_option backward.isDefEq.respectTransparency false

/-- Apply the local C1,2 proof to the actual logarithmic stock and its
 constructed compact-interval exit time. -/
theorem affine_pde_compact_stop {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (y a σ a0 R U l x0 x1 u : ℝ)
    (ha0 : a0<0) (hR : 0≤R) (hRU : R<U)
    (hl : l<x0) (hy0 : x0<y) (hy1 : y<x1) (hu : x1<u)
    (v : ℝ → ℝ → ℝ) (vt : ℝ × ℝ → ℝ)
    (hv : ∀ t∈Ioo a0 U,ContDiffOn ℝ 2 (v t) (Ioo l u))
    (hvt : ∀ t∈Ioo a0 U,∀ x∈Ioo l u,HasDerivAt (fun s => v s x) (vt (t,x)) t)
    (hvc : ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (Ioo a0 U ×ˢ Ioo l u))
    (hvtc : ContinuousOn vt (Ioo a0 U ×ˢ Ioo l u))
    (hdxc : ContinuousOn (fun z : ℝ × ℝ => deriv (v z.1) z.2) (Ioo a0 U ×ˢ Ioo l u))
    (hxxc : ContinuousOn (fun z : ℝ × ℝ => deriv (deriv (v z.1)) z.2) (Ioo a0 U ×ˢ Ioo l u))
    (hpde : ∀ t∈Icc 0 R,∀ z∈Icc x0 x1,vt (t,z)+deriv (v t) z*a+deriv (deriv (v t)) z*σ^2/2=0)
    (K : ℝ) (hbound : ∀ t∈Icc 0 R,∀ z∈Icc x0 x1,|v t z|≤K) :
    let X := fun t w => y+a*B.C 0 0 t w+σ*B.W 0 t w
    ∃ τ : Ω → Icc (0:ℝ) R,∃ N : HalfClosedTime → Ω → ℝ,
      (∀ w,realTimeClamp (τ w).val=min (intervalExit (fun s => X s w) x0 x1) (realTimeClamp R)) ∧
      ContinuousM2Witness P B.F N ∧
      (∀ᵐ w ∂P,∀ r∈Icc 0 R,
        v (min (τ w).val r) (X (realTimeClamp (min (τ w).val r)) w)=v 0 y+N (realTimeClamp r) w) := by
  dsimp only
  let X := fun t w => y+a*B.C 0 0 t w+σ*B.W 0 t w
  let A := fun t w => y+a*B.C 0 0 t w
  let M := fun t w => σ*B.W 0 t w
  obtain ⟨hX,hC,hAe,hCe,hinit⟩ := affine_brownian_decomposition P B (fun _ => y) measurable_const a σ
  have hXa t (ht : t<⊤) : Measurable[B.F t] (X t) := by
    have he : X t=fun w => A t w+M t w := funext (hX.decomposition t ht)
    rw [he]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P B.F t ht)
  let ζ := fun w => min (intervalExit (fun s => X s w) x0 x1) (realTimeClamp R)
  have hζt w : ζ w<⊤ := (min_le_right _ _).trans_lt (real_time_below R hR (EReal.coe_lt_top R))
  choose q hq hqt hqe using fun w => finite_closed_time_real (ζ w) (hζt w)
  have hqR w : q w≤R := by
    have hh : realTimeClamp (T:=(⊤:EReal)) (q w)≤realTimeClamp R := hqe w ▸ min_le_right _ _
    change (realTimeClamp (q w):EReal)≤(realTimeClamp R:EReal) at hh
    rw [real_time_clamp_eq _ (hq w) le_top,real_time_clamp_eq R hR le_top] at hh
    exact EReal.coe_le_coe_iff.mp hh
  let τ := fun w => (⟨q w,hq w,hqR w⟩ : Icc (0:ℝ) R)
  have hτ : ∀ t,MeasurableSet[B.F t] {w | realTimeClamp (τ w).val≤t} := by
    intro t
    simpa only [τ,hqe,ζ] using interval_exit_stopping B.F B.mono X hXa hX.continuous x0 x1 (realTimeClamp R) t
  have hpath : ∀ᵐ w ∂P,∀ r∈Icc 0 (τ w).val,X (realTimeClamp r) w∈Icc x0 x1 := by
    filter_upwards [hinit] with w hw
    intro r hr
    apply before_interval_exit_bounds (fun t => X t w) (hX.continuous w) x0 x1
      (by simpa only [X,hw] using And.intro hy0 hy1) r hr.1
    have hh : realTimeClamp (T:=(⊤:EReal)) r≤realTimeClamp (τ w).val := real_time_clamp_mono hr.2
    exact hh.trans ((hqe w).le.trans (min_le_left _ _))
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨N,hN,he⟩ := local_c12_stopped_representation P hT B.F B.mono B.le B.null
    X A M (fun t w => σ^2*B.C 0 0 t w) hX hC
    a0 R U l x0 x1 u ha0 hR hRU hl (hy0.trans hy1).le hu v vt hv hvt hvc hvtc hdxc hxxc
    (EReal.coe_lt_top R) c (fun n => (hc n).le) hcm.monotone hcT hcc
    (fun _ => a) (fun _ => σ^2) (fun _ => measurable_const) (fun _ => measurable_const)
    (fun _ => ae_of_all _ fun _ => intervalIntegrable_const) (fun _ => ae_of_all _ fun _ => intervalIntegrable_const)
    (fun n => ae_of_all _ fun w r hr => hAe w r hr.1)
    (fun n => ae_of_all _ fun w r hr => hCe w r hr.1) τ hτ hpath
    (hpath.mono fun w hw t ht => hpde t ⟨ht.1,ht.2.trans (τ w).property.2⟩ _ (hw t ht)) K
    (hpath.mono fun w hw t ht => hbound t ⟨ht.1,ht.2.trans (τ w).property.2⟩ _ (hw t ht))
  refine ⟨τ,N,hqe,hN,?_⟩
  filter_upwards [he,hinit] with w hw hi
  intro r hr
  have hi' : X ⊥ w=y := hi
  simpa only [hi',X] using hw r hr

end Asakura.Chapter11
