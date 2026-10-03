import Chapter12GaussianJets
import Chapter12DerivativeGrowthAlgebra
import Chapter12DerivativeGrowthProduct
import Chapter12LinearCylinder

open MeasureTheory
open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def GaussianJet.add {n : ℕ} (f g : GaussianJet n) : GaussianJet n :=
  ⟨fun x => f.f x+g.f x,f.smooth.add g.smooth,
    iterated_polynomial_growth_add f.f g.f f.smooth g.smooth f.growth g.growth⟩

noncomputable def GaussianJet.mul {n : ℕ} (f g : GaussianJet n) : GaussianJet n :=
  ⟨fun x => f.f x*g.f x,f.smooth.mul g.smooth,
    iterated_polynomial_growth_mul f.f g.f f.smooth g.smooth f.growth g.growth⟩

noncomputable def GaussianJet.smul {n : ℕ} (a : ℝ) (f : GaussianJet n) : GaussianJet n := by
  refine ⟨fun x => a*f.f x,contDiff_const.mul f.smooth,fun k => ?_⟩
  obtain ⟨C,hC,b,hb⟩ := f.growth k
  refine ⟨‖a‖*C,mul_nonneg (norm_nonneg _) hC,b,fun x => ?_⟩
  change ‖iteratedFDeriv ℝ k (fun x => a • f.f x) x‖≤_
  rw [iteratedFDeriv_const_smul_apply' (f.smooth.of_le (by simp)).contDiffAt,norm_smul]
  calc
    _≤‖a‖*(C*(1+‖x‖)^b) := mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
    _=_ := by ring

noncomputable def GaussianJet.coordinate {n : ℕ} (i : Fin n) : GaussianJet n :=
  ⟨fun x => x i,(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).contDiff,
    linear_map_all_derivatives_growth (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)⟩

noncomputable def GaussianJet.zero (n : ℕ) : GaussianJet n := by
  refine ⟨fun _ => 0,contDiff_const,fun k => ⟨0,le_rfl,0,?_⟩⟩
  intro x
  cases k <;> simp [norm_iteratedFDeriv_zero,iteratedFDeriv_succ_const]

noncomputable def GaussianJet.finsetSum {n : ℕ} {J : Type*}
    (s : Finset J) (f : J → GaussianJet n) : GaussianJet n := by
  classical
  refine ⟨fun x => ∑ j∈s,(f j).f x,ContDiff.sum (fun j _ => (f j).smooth),?_⟩
  induction s using Finset.induction_on with
  | empty => exact (GaussianJet.zero n).growth
  | @insert a s ha ih =>
    have hh := iterated_polynomial_growth_add (f a).f (fun x => ∑ j∈s,(f j).f x)
      (f a).smooth (ContDiff.sum (fun j _ => (f j).smooth)) (f a).growth ih
    simpa only [Finset.sum_insert ha] using hh

noncomputable def GaussianJet.divergence {n : ℕ} (u : Fin n → GaussianJet n) : GaussianJet n :=
  GaussianJet.finsetSum Finset.univ (fun i =>
    ((GaussianJet.coordinate i).mul (u i)).add (((u i).partial i).smul (-1)))

@[simp] theorem GaussianJet.divergence_apply {n : ℕ} (u : Fin n → GaussianJet n) (x : Fin n → ℝ) :
    (GaussianJet.divergence u).f x=∑ i,(x i*(u i).f x-((u i).partial i).f x) := by
  simp [GaussianJet.divergence,GaussianJet.finsetSum,GaussianJet.add,GaussianJet.mul,
    GaussianJet.coordinate,GaussianJet.smul,sub_eq_add_neg]

end Asakura.Chapter12
