import Chapter12GaussianJets

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_partial_frechet {N : ℕ} (f : GaussianJet N) (k : ℕ)
    (a : Fin k → Fin N) (x : Fin N → ℝ) :
    (f.iteratedPartial (List.ofFn a)).f x=
      iteratedFDeriv ℝ k f.f x (fun i => Pi.single (a i) 1) := by
  induction k generalizing x with
  | zero => simp [GaussianJet.iteratedPartial,iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ,GaussianJet.iteratedPartial]
    change fderiv ℝ (f.iteratedPartial (List.ofFn (fun i => a i.succ))).f x (Pi.single (a 0) 1)=_
    have he : (f.iteratedPartial (List.ofFn (fun i => a i.succ))).f=
        fun y => iteratedFDeriv ℝ k f.f y (fun i => Pi.single (a i.succ) 1) :=
      funext (fun y => ih (fun i => a i.succ) y)
    rw [he]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f.f) x :=
      f.smooth.contDiffAt.differentiableAt_iteratedFDeriv (m:=k) (by exact_mod_cast ENat.natCast_lt_top k)
    exact (hd.iteratedFDeriv_succ_apply_left' (m:=fun i => Pi.single (a i) 1)).symm
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussian_partial_frechet
