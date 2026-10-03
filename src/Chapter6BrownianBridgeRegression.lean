import Chapter7ClockHalfTime
import Chapter6BrownianGridSamplesGaussian
import Chapter6GaussianBridgeRegression

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The regression used in the manuscript's left-endpoint Ito sums,
proved for the actual Brownian motion at the grid times. -/
theorem brownian_bridge_grid_regression {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (h : ℝ) (hh : 0<h) (k : ℕ) (hk : k<n) (j : Fin d) :
    let Y := fun w (p : Bool × Fin d) => B.W p.2 (realTimeClamp (if p.1 then (n:ℝ)*h else (k:ℝ)*h)) w
    P[(fun w => B.W j (realTimeClamp (((k:ℝ)+1)*h)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w)|MeasurableSpace.comap Y inferInstance]=ᵐ[P]
      fun w => h/((n:ℝ)*h-(k:ℝ)*h)*(B.W j (realTimeClamp ((n:ℝ)*h)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w) := by
  let times : Fin 3 × Fin d → ℕ := fun p => if p.1=0 then k else if p.1=1 then k+1 else n
  have ht p : times p≤n := by dsimp [times]; split_ifs <;> omega
  let X := fun w (p : Fin 3 × Fin d) => B.W p.2 (realTimeClamp ((times p:ℝ)*h)) w
  obtain ⟨hg,hm,hcov⟩ := brownian_grid_samples_gaussian P B h hh.le times ht (fun p => p.2)
  let LI : ((Fin 3 × Fin d) → ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.proj ((1:Fin 3),j) : ((Fin 3 × Fin d) → ℝ) →L[ℝ] ℝ)-(ContinuousLinearMap.proj ((0:Fin 3),j) : ((Fin 3 × Fin d) → ℝ) →L[ℝ] ℝ)
  let LY : ((Fin 3 × Fin d) → ℝ) →L[ℝ] ((Bool × Fin d) → ℝ) :=
    ContinuousLinearMap.pi (fun p : Bool × Fin d => (ContinuousLinearMap.proj ((if p.1 then (2:Fin 3) else 0),p.2) : ((Fin 3 × Fin d) → ℝ) →L[ℝ] ℝ))
  have hXY := hg.map (LI.prod LY)
  let Y := fun w (p : Bool × Fin d) => B.W p.2 (realTimeClamp (if p.1 then (n:ℝ)*h else (k:ℝ)*h)) w
  let I := fun w => B.W j (realTimeClamp (((k:ℝ)+1)*h)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w
  have he : (fun w => (LI (X w),LY (X w)))=(fun w => (I w,Y w)) := by
    funext w
    apply Prod.ext
    · simp [LI,X,I,times,Nat.cast_add,Nat.cast_one]
    · funext p
      rcases p with ⟨b,i⟩
      cases b <;> simp [LY,X,Y,times]
  have hG : HasGaussianLaw (fun w => (I w,Y w)) P := by
    change HasGaussianLaw (fun w => (LI (X w),LY (X w))) P at hXY
    rwa [he] at hXY
  have hWa (i : Fin d) (a : ℕ) : Measurable (B.W i (realTimeClamp ((a:ℝ)*h))) :=
    ((B.martingale i).adapted P B.F _ (changed_time_finite _ (mul_nonneg (Nat.cast_nonneg a) hh.le))).mono (B.le _) le_rfl
  have hIm : Measurable I := by simpa only [I,Nat.cast_add,Nat.cast_one,Pi.sub_def] using (hWa j (k+1)).sub (hWa j k)
  have hYm : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro p
    rcases p with ⟨b,i⟩
    cases b
    · exact hWa i k
    · exact hWa i n
  have hi0 : (∫ w,I w ∂P)=0 := by
    have h1 := hm (1,j)
    have h0 := hm (0,j)
    have hi1 := (hg.eval (1,j)).integrable
    have hi0 := (hg.eval (0,j)).integrable
    have hh := integral_sub hi1 hi0
    simp only [X,times,ite_true,ite_false,show ¬(1:Fin 3)=0 by decide,Nat.cast_add,Nat.cast_one] at h1 h0 hh
    change (∫ w,I w ∂P)=_ at hh
    rw [hh,h1,h0,sub_self]
  have hy0 p : (∫ w,Y w p ∂P)=0 := by
    have hz := hm ((if p.1 then 2 else 0),p.2)
    rcases p with ⟨b,i⟩
    cases b <;> simpa [Y,times] using hz
  have hYY p q : cov[(fun w => Y w p),(fun w => Y w q);P]=
      if p.2=q.2 then (if p.1 && q.1 then (n:ℝ)*h else (k:ℝ)*h) else 0 := by
    have hv := hcov ((if p.1 then 2 else 0),p.2) ((if q.1 then 2 else 0),q.2)
    rcases p with ⟨b,i⟩
    rcases q with ⟨a,j⟩
    cases b <;> cases a <;> simpa [Y,times,min_eq_left hk.le,min_eq_right hk.le] using hv
  have hIY p : cov[I,(fun w => Y w p);P]=if p.1 && decide (p.2=j) then h else 0 := by
    have hv := covariance_sub_left (hg.eval (1,j)).memLp_two (hg.eval (0,j)).memLp_two
      (hg.eval ((if p.1 then 2 else 0),p.2)).memLp_two
    rw [hcov,hcov] at hv
    rcases p with ⟨b,i⟩
    cases b <;> by_cases heq : i=j
    · subst heq
      simpa [I,Y,times,Pi.sub_def,min_eq_right (Nat.le_succ k),min_eq_left (Nat.le_succ k),Nat.cast_add,Nat.cast_one] using hv
    · simpa [I,Y,times,Pi.sub_def,heq,Ne.symm heq] using hv
    · subst heq
      simpa [I,Y,times,Pi.sub_def,min_eq_left hk.le,min_eq_left (Nat.succ_le_of_lt hk),Nat.cast_add,Nat.cast_one,add_mul] using hv
    · simpa [I,Y,times,Pi.sub_def,heq,Ne.symm heq] using hv
  have hst : (k:ℝ)*h<(n:ℝ)*h := mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hk) hh
  exact gaussian_bridge_increment_regression P I Y j hG hIm hYm ((k:ℝ)*h) ((n:ℝ)*h) h hst hi0 hy0 hYY hIY

end Asakura.Chapter6
