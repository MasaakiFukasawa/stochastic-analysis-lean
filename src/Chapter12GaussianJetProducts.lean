import Chapter12GaussianJetCommutation

open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def GaussianJet.constant (n : ℕ) (a : ℝ) : GaussianJet n := by
  refine ⟨fun _ => a,contDiff_const,fun k => ⟨‖a‖,norm_nonneg _,0,?_⟩⟩
  intro x
  cases k <;> simp [norm_iteratedFDeriv_zero,iteratedFDeriv_succ_const]

noncomputable def GaussianJet.listProd {n : ℕ} : List (GaussianJet n) → GaussianJet n
  | [] => GaussianJet.constant n 1
  | f::fs => f.mul (GaussianJet.listProd fs)

@[simp] theorem GaussianJet.listProd_apply {n : ℕ} (fs : List (GaussianJet n)) (x : Fin n → ℝ) :
    (GaussianJet.listProd fs).f x=(fs.map (fun f => f.f x)).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simpa only [GaussianJet.listProd,GaussianJet.mul,List.map_cons,List.prod_cons] using congrArg (fun a => f.f x*a) ih

theorem GaussianJet.mul_partial {n : ℕ} (f g : GaussianJet n) (i : Fin n) (x : Fin n → ℝ) :
    ((f.mul g).partial i).f x=(f.partial i).f x*g.f x+f.f x*(g.partial i).f x := by
  change (fderiv ℝ (f.f*g.f) x) (Pi.single i 1)=_
  rw [fderiv_mul ((f.smooth.differentiable (by simp)).differentiableAt)
    ((g.smooth.differentiable (by simp)).differentiableAt)]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,GaussianJet.partial]
  ring

@[simp] theorem GaussianJet.constant_partial {n : ℕ} (a : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    ((GaussianJet.constant n a).partial i).f x=0 := by
  simp [GaussianJet.constant,GaussianJet.partial]

end Asakura.Chapter12
