import Chapter7BrownianProductEnergy
import Chapter7BrownianVectorIndependence
import Chapter7OrthogonalSquareSum

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- The exact mean-square error of the Brownian part of one matrix entry
of the realized covariance estimator, before division by the horizon. -/
theorem brownian_product_grid_energy {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (h : ℝ) (hh : 0 ≤ h) :
    let D := fun k : Fin n => fun w j =>
      B.W j (realTimeClamp (((k:ℝ)+1)*h)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w
    let Z := fun k w => (∑ j,u j*D k w j)*(∑ j,v j*D k w j)-h*(∑ j,u j*v j)
    MemLp (fun w => ∑ k,Z k w) 2 P ∧
    (∫ w,(∑ k,Z k w)^2 ∂P)=(n:ℝ)*h^2*((∑ j,u j^2)*(∑ j,v j^2)+(∑ j,u j*v j)^2) := by
  classical
  dsimp only
  let t := fun k : ℕ => (k:ℝ)*h
  have ht k : 0 ≤ t k := mul_nonneg (Nat.cast_nonneg _) hh
  have htm : Monotone t := fun k l hkl => mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkl) hh
  have hstep k : t (k+1)-t k=h := by dsimp [t]; push_cast; ring
  let D := fun k : Fin n => fun w j => B.W j (realTimeClamp (t (k.val+1))) w-B.W j (realTimeClamp (t k.val)) w
  let f := fun x : Fin d → ℝ => (∑ j,u j*x j)*(∑ j,v j*x j)-h*(∑ j,u j*v j)
  let Z := fun k w => f (D k w)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he (k : Fin n) : MemLp (Z k) 2 P ∧ (∫ w,Z k w ∂P)=0 ∧
      (∫ w,Z k w^2 ∂P)=h^2*((∑ j,u j^2)*(∑ j,v j^2)+(∑ j,u j*v j)^2) := by
    simpa only [Z,f,D,hstep] using brownian_product_energy P B (t k.val) (t (k.val+1)) (ht _) (htm (Nat.le_succ _)) u v
  have hZa (k l : Fin n) (hkl : k.val+1 ≤ l.val) : Measurable[B.F (realTimeClamp (t l.val))] (Z k) := by
    letI : MeasurableSpace Ω := B.F (realTimeClamp (t l.val))
    apply hf.comp
    apply measurable_pi_iff.mpr
    intro j
    apply Measurable.sub
    · exact ((B.martingale j).adapted P B.F _ (real_time_below _ (ht _) (EReal.coe_lt_top _))).mono
        (B.mono (real_time_clamp_mono (htm hkl))) le_rfl
    · exact ((B.martingale j).adapted P B.F _ (real_time_below _ (ht _) (EReal.coe_lt_top _))).mono
        (B.mono (real_time_clamp_mono (htm ((Nat.le_succ _).trans hkl)))) le_rfl
  have hZi (k : Fin n) : Indep (MeasurableSpace.comap (Z k) inferInstance) (B.F (realTimeClamp (t k.val))) P :=
    independent_measurable_transform P _ (D k) f
      (brownian_vector_increment_independent P B (t k.val) (t (k.val+1)) (ht _) (htm (Nat.le_succ _))) hf
  have horth (k l : Fin n) (hkl : k < l) : (∫ w,Z k w*Z l w ∂P)=0 := by
    have h := independent_centered_cross P _ (Z l) (Z k) (fun _ => 1)
      (hZi l) (hZa k l hkl) measurable_const ((he l).1.integrable (by norm_num))
      (by simpa only [mul_one] using (he k).1.integrable (by norm_num)) (he l).2.1
    simpa only [one_mul] using h
  have hsum := orthogonal_square_sum P Finset.univ Z (fun k _ => (he k).1) (by
    intro k _ l _ hne
    rcases lt_or_gt_of_ne hne with hlt|hgt
    · exact horth k l hlt
    · simpa only [mul_comm] using horth l k hgt)
  have hh' : (∫ w,(∑ k,Z k w)^2 ∂P)=(n:ℝ)*h^2*((∑ j,u j^2)*(∑ j,v j^2)+(∑ j,u j*v j)^2) := by
    rw [hsum]
    simp only [(he _).2.2,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hm : MemLp (fun w => ∑ k,Z k w) 2 P := by
    convert memLp_finsetSum' Finset.univ (fun k _ => (he k).1) using 1
    ext w
    simp
  simpa only [Z,f,D,t,Nat.cast_add,Nat.cast_one] using And.intro hm hh'

end Asakura.Chapter7
