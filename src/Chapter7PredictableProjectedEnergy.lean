import Chapter7OrthogonalSquareSum
import Chapter7BrownianProjectionLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- Exact square moment of a predictable weighted Brownian grid sum, from
the actual Brownian filtration and increments, not an orthogonality premise. -/
theorem predictable_projected_grid_energy {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (h : ℝ) (hh : 0 ≤ h) (G : Fin n → Ω → ℝ)
    (hGa : ∀ k : Fin n,Measurable[B.F (realTimeClamp ((k:ℝ)*h))] (G k))
    (hG : ∀ k,MemLp (G k) 2 P) :
    let Z := fun k : Fin n => fun w =>
      ∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*h)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w)
    (∫ w,(∑ k,G k w*Z k w)^2 ∂P)=h*(∑ j,u j^2)*(∑ k,∫ w,G k w^2 ∂P) := by
  classical
  dsimp only
  let t := fun k : ℕ => (k:ℝ)*h
  have ht k : 0 ≤ t k := mul_nonneg (Nat.cast_nonneg _) hh
  have htm : Monotone t := fun k l hkl => mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkl) hh
  let Z := fun k : Fin n => fun w => ∑ j,u j*(B.W j (realTimeClamp (t (k.val+1))) w-B.W j (realTimeClamp (t k.val)) w)
  have hZlaw (k : Fin n) := brownian_projection_law P B (t k.val) (t (k.val+1)) (ht _) (htm (Nat.le_succ _)) u
  have he (k : Fin n) := gaussian_weighted_increment_energy P (G k) (Z k) (hG k) _ (hZlaw k).1
    (indepFun_of_independent_information P _ (Z k) (G k) (hZlaw k).2 (hGa k)).symm
  have hZa (k l : Fin n) (hkl : k.val+1 ≤ l.val) : Measurable[B.F (realTimeClamp (t l.val))] (Z k) := by
    apply Finset.measurable_sum
    intro j _
    apply measurable_const.mul
    apply Measurable.sub
    · exact ((B.martingale j).adapted P B.F _ (real_time_below _ (ht _) (EReal.coe_lt_top _))).mono
        (B.mono (real_time_clamp_mono (htm hkl))) le_rfl
    · exact ((B.martingale j).adapted P B.F _ (real_time_below _ (ht _) (EReal.coe_lt_top _))).mono
        (B.mono (real_time_clamp_mono (htm ((Nat.le_succ _).trans hkl)))) le_rfl
  have horth (k l : Fin n) (hkl : k < l) :
      (∫ w,(G k w*Z k w)*(G l w*Z l w) ∂P)=0 := by
    have hUa : Measurable[B.F (realTimeClamp (t l.val))] (fun w => G k w*Z k w) :=
      ((hGa k).mono (B.mono (real_time_clamp_mono (htm hkl.le))) le_rfl).mul (hZa k l hkl)
    have huv := (he k).1.integrable_mul (hG l)
    have hmean : (∫ w,Z l w ∂P)=0 := by
      have hh' := (hZlaw l).1.integral_eq
      simpa only [integral_id_gaussianReal] using hh'
    exact independent_centered_cross P _ (Z l) (fun w => G k w*Z k w) (G l)
      (hZlaw l).2 hUa (hGa l) ((hZlaw l).1.memLp (memLp_id_gaussianReal 2) |>.integrable (by norm_num))
      huv hmean
  have hsum := orthogonal_square_sum P Finset.univ (fun k w => G k w*Z k w)
    (fun k _ => (he k).1) (by
      intro k _ l _ hne
      rcases lt_or_gt_of_ne hne with hlt|hgt
      · exact horth k l hlt
      · simpa only [mul_comm] using horth l k hgt)
  have hstep k : t (k+1)-t k=h := by dsimp [t]; push_cast; ring
  have hsum' : (∫ w,(∑ k,G k w*Z k w)^2 ∂P)=h*(∑ j,u j^2)*(∑ k,∫ w,G k w^2 ∂P) := by
    rw [hsum,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by simpa only [NNReal.toReal,hstep] using (he k).2)
  simpa only [Z,t,Nat.cast_add,Nat.cast_one] using hsum'

end Asakura.Chapter7
