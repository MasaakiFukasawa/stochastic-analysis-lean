import Chapter12GaussianIndexedVectorMoment

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

noncomputable def gaussianArrayLp {n : ℕ} {I : Type*} [Fintype I]
    (f : I → GaussianJet n) (p : ℝ≥0∞) (hp : p≠⊤) :
    Lp ℝ p (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
  (polynomial_growth_gaussian_memLp (gaussianArrayNorm_continuous f).measurable
    (gaussianArrayNorm_growth f) p hp).toLp (gaussianArrayNorm f)

theorem gaussianArrayLp_coe {n : ℕ} {I : Type*} [Fintype I]
    (f : I → GaussianJet n) (p : ℝ≥0∞) (hp : p≠⊤) :
    (gaussianArrayLp f p hp : (Fin n → ℝ) → ℝ)=ᵐ[Measure.pi (fun _ => gaussianReal 0 1)]
      gaussianArrayNorm f :=
  (polynomial_growth_gaussian_memLp (gaussianArrayNorm_continuous f).measurable
    (gaussianArrayNorm_growth f) p hp).coeFn_toLp

theorem gaussianArrayLp_norm_coe {n : ℕ} {I : Type*} [Fintype I]
    (f : I → GaussianJet n) (p : ℝ≥0∞) (hp : p≠⊤) :
    (fun x => ‖gaussianArrayLp f p hp x‖)=ᵐ[Measure.pi (fun _ => gaussianReal 0 1)]
      gaussianArrayNorm f := by
  filter_upwards [gaussianArrayLp_coe f p hp] with x hx
  rw [hx,Real.norm_eq_abs,abs_of_nonneg (gaussianArrayNorm_nonneg _ _)]

/-- The vector moment inequality gives the printed sum of actual Lp norms. -/
theorem indexed_vector_divergence_Lp_bound {n : ℕ} {I : Type*} [Fintype I]
    (u : I → Fin (n+1) → GaussianJet (n+1)) (p : ℕ) (hp : 0<p)
    [Fact (1≤((2*p:ℕ):ℝ≥0∞))] :
    ‖gaussianArrayLp (fun a => GaussianJet.divergence (u a)) (2*p:ℕ) (ENNReal.natCast_ne_top _)‖ ≤
    (2*(2*p-1):ℕ)*∑ j : Fin (2*p+1),
      ‖gaussianArrayLp (fun ab : I × (Fin (j.val+1) → Fin (n+1)) =>
        gaussianDerivativeArray (u ab.1) j ab.2) (2*p:ℕ) (ENNReal.natCast_ne_top _)‖ := by
  let z := gaussianArrayLp (fun a => GaussianJet.divergence (u a)) (2*p:ℕ) (ENNReal.natCast_ne_top _)
  let v := fun j : Fin (2*p+1) => gaussianArrayLp
    (fun ab : I × (Fin (j.val+1) → Fin (n+1)) => gaussianDerivativeArray (u ab.1) j ab.2)
    (2*p:ℕ) (ENNReal.natCast_ne_top _)
  apply moment_to_sobolev_norm (2*p) (by omega) z v (2*(2*p-1):ℕ) (by positivity)
  have hz : (fun x => |z x|)=ᵐ[Measure.pi (fun _ => gaussianReal 0 1)]
      gaussianArrayNorm (fun a => GaussianJet.divergence (u a)) :=
    gaussianArrayLp_norm_coe _ _ _
  have hv := ae_all_iff.mpr (fun j : Fin (2*p+1) => gaussianArrayLp_norm_coe
    (fun ab : I × (Fin (j.val+1) → Fin (n+1)) => gaussianDerivativeArray (u ab.1) j ab.2)
    (2*p:ℕ) (ENNReal.natCast_ne_top _))
  have hleft := integral_congr_ae (hz.fun_comp (fun a => a^(2*p)))
  simp only [Function.comp_def] at hleft
  rw [hleft]
  have hright : (∫ x,(∑ j : Fin (2*p+1),‖v j x‖)^(2*p) ∂Measure.pi (fun _ => gaussianReal 0 1))=
      ∫ x,(∑ j : Fin (2*p+1),gaussianArrayNorm
        (fun ab : I × (Fin (j.val+1) → Fin (n+1)) => gaussianDerivativeArray (u ab.1) j ab.2) x)^(2*p)
        ∂Measure.pi (fun _ => gaussianReal 0 1) := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    congr 1
    exact Finset.sum_congr rfl (fun j _ => hx j)
  rw [hright]
  exact indexed_vector_divergence_even_moment u p hp

end Asakura.Chapter12
