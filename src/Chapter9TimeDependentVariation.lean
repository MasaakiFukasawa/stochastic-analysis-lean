import Chapter9ParametricCompactTaylor
import FullAuditChapter4Gronwall

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter9
open Asakura.FullAudit
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Differentiation of the integral equation under merely continuous
first derivatives. The initial condition may depend affinely on the
parameter. This applies to the augmented state (X,J) without assuming a
third drift derivative. -/
theorem time_dependent_variational_derivative {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (b : ℝ → F → F) (D : ℝ → F → F →L[ℝ] F)
    (hD : ∀ t z,HasFDerivAt (b t) (D t z) z) (hb : Continuous b.uncurry) (hcD : Continuous D.uncurry)
    (I : E →L[ℝ] F) (c : F) (X : E → ℝ → F) (W : ℝ → F)
    (hcX : ∀ z,Continuous (X z)) (x : E) (T A L : ℝ)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hL : 0<L)
    (hDb : ∀ s,s∈Icc 0 T → ‖D s (X x s)‖ ≤ L)
    (hX : ∀ z s,s∈Icc 0 T → X z s=I z+c+(∫ r in 0..s,b r (X z r))+W s)
    (hLip : ∀ h s,s∈Icc 0 T → ‖X (x+h) s-X x s‖ ≤ A*‖h‖)
    (J : ℝ → E →L[ℝ] F) (hcJ : Continuous J)
    (hJ : ∀ s,s∈Icc 0 T → ∀ h,J s h=I h+∫ r in 0..s,D r (X x r) (J r h)) :
    HasFDerivAt (fun z => X z T) (J T) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  let B : ℝ := A*T*Real.exp (L*T)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let η := ε/(B+1)
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hrem⟩ := parametric_compact_taylor_remainder b D hD hcD ((fun s => (s,X x s)) '' Icc 0 T)
    (isCompact_Icc.image (continuous_id.prodMk (hcX x))) η hη
  filter_upwards [Metric.ball_mem_nhds (0:E) (show 0<δ/(A+1) by positivity)] with h hh
  have hhn : ‖h‖<δ/(A+1) := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  have hAh : A*‖h‖<δ := by
    have hh' := (lt_div_iff₀ (show 0<A+1 by positivity)).mp hhn
    nlinarith [norm_nonneg h]
  let e := fun s => X (x+h) s-X x s-J s h
  let g := fun s => b s (X (x+h) s)-b s (X x s)-D s (X x s) (J s h)
  have hec : Continuous e := ((hcX (x+h)).sub (hcX x)).sub (hcJ.clm_apply continuous_const)
  have hgc : Continuous g := ((hb.comp (continuous_id.prodMk (hcX (x+h)))).sub (hb.comp (continuous_id.prodMk (hcX x)))).sub
    ((hcD.comp (continuous_id.prodMk (hcX x))).clm_apply (hcJ.clm_apply continuous_const))
  have he s (hs : s∈Icc 0 T) : e s=∫ r in 0..s,g r := by
    dsimp only [e,g]
    rw [hX (x+h) s hs,hX x s hs,hJ s hs h,map_add]
    rw [intervalIntegral.integral_sub
      (f := fun r => b r (X (x+h) r)-b r (X x r)) (g := fun r => D r (X x r) (J r h))
      (((hb.comp (continuous_id.prodMk (hcX (x+h)))).sub (hb.comp (continuous_id.prodMk (hcX x)))).intervalIntegrable 0 s)
      (((hcD.comp (continuous_id.prodMk (hcX x))).clm_apply (hcJ.clm_apply continuous_const)).intervalIntegrable 0 s),
      intervalIntegral.integral_sub (f := fun r => b r (X (x+h) r)) (g := fun r => b r (X x r))
        ((hb.comp (continuous_id.prodMk (hcX (x+h)))).intervalIntegrable 0 s)
        ((hb.comp (continuous_id.prodMk (hcX x))).intervalIntegrable 0 s)]
    abel
  let R := η*A*‖h‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hgn s (hs : s∈Icc 0 T) : ‖g s‖ ≤ L*‖e s‖+R := by
    have hr := hrem s (X x s) ⟨s,hs,rfl⟩ (X (x+h) s-X x s) ((hLip h s hs).trans_lt hAh)
    rw [add_sub_cancel] at hr
    have hr' : ‖b s (X (x+h) s)-b s (X x s)-D s (X x s) (X (x+h) s-X x s)‖ ≤ R :=
      hr.trans (by simpa only [R,mul_assoc] using mul_le_mul_of_nonneg_left (hLip h s hs) hη.le)
    have hl : ‖D s (X x s) (e s)‖ ≤ L*‖e s‖ :=
      ((D s (X x s)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hDb s hs) (norm_nonneg _))
    have hg : g s=D s (X x s) (e s)+(b s (X (x+h) s)-b s (X x s)-D s (X x s) (X (x+h) s-X x s)) := by
      dsimp only [g,e]
      simp only [map_sub]
      abel
    rw [hg]
    exact (norm_add_le _ _).trans (add_le_add hl hr')
  have hine s (hs : s∈Icc 0 T) : ‖e s‖ ≤ R*T+L*∫ r in 0..s,‖e r‖ := by
    rw [he s hs]
    have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0:ℝ)) (b := s)
      (f := g) (g := fun r => L*‖e r‖+R) hs.1
      (ae_of_all _ (fun r hr => hgn r ⟨hr.1.le,hr.2.trans hs.2⟩))
      (((hec.norm.const_mul L).add continuous_const).intervalIntegrable 0 s)
    rw [intervalIntegral.integral_add (f := fun r => L*‖e r‖) (g := fun _ => R)
      ((hec.norm.const_mul L).intervalIntegrable 0 s) intervalIntegrable_const,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hh
    have ht := mul_le_mul_of_nonneg_left hs.2 hR
    linarith
  have hgr := ch4_gronwall_written (fun s => ‖e s‖) (R*T) L T hT hec.norm.continuousOn hL hine T ⟨hT,le_rfl⟩
  have hηB : η*B ≤ ε := by
    have he : η*(B+1)=ε := by dsimp [η]; field_simp
    nlinarith
  have heq : R*T*Real.exp (L*T)=(η*B)*‖h‖ := by dsimp [R,B]; ring
  rw [heq] at hgr
  exact hgr.trans (mul_le_mul_of_nonneg_right hηB (norm_nonneg h))

end Asakura.Chapter9
