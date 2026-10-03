import Chapter12GaussianArrayLp
import Chapter12GaussianDerivativeFlatten

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

theorem gaussianArrayLp_congr {n : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (f : I → GaussianJet n) (g : J → GaussianJet n)
    (p : ℝ≥0∞) (hp : p≠⊤) (h : ∀ x,gaussianArrayNorm f x=gaussianArrayNorm g x) :
    gaussianArrayLp f p hp=gaussianArrayLp g p hp := by
  apply Lp.ext
  filter_upwards [gaussianArrayLp_coe f p hp,gaussianArrayLp_coe g p hp] with x hf hg
  rw [hf,hg,h]

/-- All derivative orders of the actual finite Gaussian divergence obey
the estimate printed in the manuscript. -/
theorem gaussian_higher_divergence_Lp_bound {n k : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (p : ℕ) (hp : 0<p)
    [Fact (1≤((2*p:ℕ):ℝ≥0∞))] :
    ‖gaussianArrayLp (fun b : Fin (k+1) → Fin (n+1) =>
      (GaussianJet.divergence u).iteratedPartial (List.ofFn b)) (2*p:ℕ) (ENNReal.natCast_ne_top _)‖ ≤
    (k+1:ℕ)*‖gaussianArrayLp (gaussianDerivativeArray u k) (2*p:ℕ) (ENNReal.natCast_ne_top _)‖+
    (2*(2*p-1):ℕ)*∑ j : Fin (2*p+1),
      ‖gaussianArrayLp (gaussianDerivativeArray u (j.val+(k+1))) (2*p:ℕ) (ENNReal.natCast_ne_top _)‖ := by
  let L := gaussianArrayLp (fun b : Fin (k+1) → Fin (n+1) =>
    (GaussianJet.divergence u).iteratedPartial (List.ofFn b)) (2*p:ℕ) (ENNReal.natCast_ne_top _)
  let U := gaussianArrayLp (gaussianDerivativeArray u k) (2*p:ℕ) (ENNReal.natCast_ne_top _)
  let G := gaussianArrayLp (fun b : Fin (k+1) → Fin (n+1) =>
    GaussianJet.divergence (fun i => (u i).iteratedPartial (List.ofFn b)))
    (2*p:ℕ) (ENNReal.natCast_ne_top _)
  have hpoint : ‖L‖≤‖(k+1:ℝ) • U+G‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [gaussianArrayLp_norm_coe (fun b : Fin (k+1) → Fin (n+1) =>
        (GaussianJet.divergence u).iteratedPartial (List.ofFn b)) (2*p:ℕ) (ENNReal.natCast_ne_top _),
      gaussianArrayLp_coe (gaussianDerivativeArray u k) (2*p:ℕ) (ENNReal.natCast_ne_top _),
      gaussianArrayLp_coe (fun b : Fin (k+1) → Fin (n+1) =>
        GaussianJet.divergence (fun i => (u i).iteratedPartial (List.ofFn b)))
          (2*p:ℕ) (ENNReal.natCast_ne_top _),
      Lp.coeFn_add ((k+1:ℝ) • U) G,Lp.coeFn_smul (k+1:ℝ) U] with x hL hU hG hadd hsmul
    change ‖L x‖≤‖((k+1:ℝ) • U+G) x‖
    rw [hL,hadd,Pi.add_apply,hsmul,Pi.smul_apply,hU,hG,smul_eq_mul,Real.norm_eq_abs]
    rw [abs_of_nonneg (add_nonneg (mul_nonneg (by positivity : 0≤(k+1:ℝ)) (gaussianArrayNorm_nonneg _ _)) (gaussianArrayNorm_nonneg _ _))]
    simpa only [gaussianDerivativeNorm,Nat.cast_add,Nat.cast_one] using gaussian_commutator_norm_bound (k:=k) u x
  have htri : ‖L‖≤(k+1:ℕ)*‖U‖+‖G‖ := hpoint.trans (by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(k+1:ℝ)),Nat.cast_add,Nat.cast_one]
      using norm_add_le ((k+1:ℝ) • U) G)
  have hG := indexed_vector_divergence_Lp_bound
    (fun (b : Fin (k+1) → Fin (n+1)) i => (u i).iteratedPartial (List.ofFn b)) p hp
  have hj (j : Fin (2*p+1)) :
      gaussianArrayLp (fun ab : (Fin (k+1) → Fin (n+1)) × (Fin (j.val+1) → Fin (n+1)) =>
        gaussianDerivativeArray (fun i => (u i).iteratedPartial (List.ofFn ab.1)) j ab.2)
          (2*p:ℕ) (ENNReal.natCast_ne_top _) =
      gaussianArrayLp (gaussianDerivativeArray u (j.val+(k+1))) (2*p:ℕ) (ENNReal.natCast_ne_top _) := by
    apply gaussianArrayLp_congr
    exact gaussian_higher_derivative_flatten u j (k+1)
  have hG' := hG
  simp only [hj] at hG'
  exact htri.trans (add_le_add le_rfl hG')

end Asakura.Chapter12
