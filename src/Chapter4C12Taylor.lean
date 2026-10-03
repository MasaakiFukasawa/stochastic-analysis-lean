import Chapter3FiniteDimensionalTaylor
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter4
open Asakura.Chapter3Complete Asakura.Chapter3Written
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Uniform Taylor control for C1 in time and C2 in space. No mixed or
second time derivative occurs in the assumptions or the remainder. -/
theorem c12_uniform_taylor {dim : ℕ}
    (f : ℝ → (Fin dim → ℝ) → ℝ) (ft : ℝ × (Fin dim → ℝ) → ℝ)
    (hf : ∀ t,ContDiff ℝ 2 (f t))
    (hft : ∀ t x,HasDerivAt (fun s => f s x) (ft (t,x)) t)
    (hftc : Continuous ft)
    (hhc : Continuous (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (f z.1)) z.2))
    (R ε : ℝ) (hε : 0<ε) :
    ∃ δ>0,∀ a∈Icc 0 R,∀ b∈Icc 0 R,a≤b → ∀ x∈Metric.closedBall 0 R,∀ y∈Metric.closedBall 0 R,
      b-a≤δ → ‖y-x‖≤δ →
      |f b y-f a x-ft (a,x)*(b-a)-(fderiv ℝ (f a) x) (y-x)-
        (fderiv ℝ (fderiv ℝ (f a)) x) (y-x) (y-x)/2|
      ≤ ε*(b-a)+ε*‖y-x‖^2/2 := by
  let K : Set (ℝ × (Fin dim → ℝ)) := (Icc 0 R) ×ˢ Metric.closedBall 0 R
  have hk : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨δ1,hδ1,ht⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hk.uniformContinuousOn_of_continuous hftc.continuousOn) ε hε
  have huH := hk.uniformContinuousOn_of_continuous (f := fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (f z.1)) z.2) hhc.continuousOn
  obtain ⟨δ2,hδ2,hH⟩ := (Metric.uniformContinuousOn_iff_le (f := fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (f z.1)) z.2)).mp huH ε hε
  refine ⟨min δ1 δ2,lt_min hδ1 hδ2,?_⟩
  intro a ha b hb hab x hx y hy hdt hxy
  have htaylor : |f a y-f a x-(fderiv ℝ (f a) x) (y-x)-
      (fderiv ℝ (fderiv ℝ (f a)) x) (y-x) (y-x)/2|≤ε*‖y-x‖^2/2 := by
    have hs := multivariate_taylor_remainder (hf a) x (y-x) hε.le
    simp only [add_sub_cancel] at hs
    apply hs
    intro t ht'
    have hmem : x+t • (y-x)∈Metric.closedBall 0 R :=
      (convex_closedBall (0 : Fin dim → ℝ) R).add_smul_mem hx (by simpa using hy) ht'
    have hbnd : dist (a,x+t • (y-x)) (a,x)≤δ2 := by
      rw [Prod.dist_eq]
      dsimp only
      rw [dist_self,max_eq_right dist_nonneg]
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht'.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht'.2).trans (hxy.trans (min_le_right _ _))
    have hh := hH (a,x+t • (y-x)) ⟨ha,hmem⟩ (a,x) ⟨ha,hx⟩ hbnd
    have heq := dist_eq_norm (fderiv ℝ (fderiv ℝ (f a)) (x+t • (y-x))) (fderiv ℝ (fderiv ℝ (f a)) x)
    exact heq ▸ hh
  have htime : |f b y-f a y-ft (a,x)*(b-a)|≤ε*(b-a) := by
    let G := fun r => ft (r,y)-ft (a,x)
    have hGc : Continuous G := (hftc.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    have hder r : HasDerivAt (fun s => f s y-ft (a,x)*s) (G r) r := by
      simpa only [G,mul_one,id_eq,Pi.sub_def] using ((hft r y).sub ((hasDerivAt_id r).const_mul (ft (a,x))))
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hder r) (hGc.intervalIntegrable a b)
    have hbound : ‖∫ r in a..b,G r‖≤ε*|b-a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => by
        have hr' : r∈Icc a b := ⟨(uIoc_of_le hab ▸ hr).1.le,(uIoc_of_le hab ▸ hr).2⟩
        have hrK : (r,y)∈K := ⟨⟨ha.1.trans hr'.1,hr'.2.trans hb.2⟩,hy⟩
        have hdist : dist (r,y) (a,x)≤δ1 := by
          rw [Prod.dist_eq]
          apply max_le
          · rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hr'.1)]
            exact (sub_le_sub_right hr'.2 a).trans (hdt.trans (min_le_left _ _))
          · exact (show dist y x≤min δ1 δ2 from hxy).trans (min_le_left _ _)
        simpa only [G,Real.norm_eq_abs,Real.dist_eq] using ht (r,y) hrK (a,x) ⟨ha,hx⟩ hdist)
    have hE : (∫ r in a..b,G r)=f b y-f a y-ft (a,x)*(b-a) := by
      convert he using 1 <;> ring
    rw [hE,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at hbound
    exact hbound
  calc
    _ = |(f b y-f a y-ft (a,x)*(b-a))+
        (f a y-f a x-(fderiv ℝ (f a) x) (y-x)-(fderiv ℝ (fderiv ℝ (f a)) x) (y-x) (y-x)/2)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add htime htaylor)

end Asakura.Chapter4
