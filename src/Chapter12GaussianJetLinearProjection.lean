import Chapter12GaussianJetProducts

open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem GaussianJet.ext_f {n : ℕ} (f g : GaussianJet n) (he : f.f=g.f) : f=g := by
  cases f
  cases g
  cases he
  rfl

theorem GaussianJet.smul_partial {n : ℕ} (f : GaussianJet n) (a : ℝ) (i : Fin n) :
    (f.smul a).partial i=(f.partial i).smul a := by
  apply GaussianJet.ext_f
  funext x
  change fderiv ℝ (a • f.f) x (Pi.single i 1)=a*(f.partial i).f x
  rw [fderiv_const_smul ((f.smooth.differentiable (by simp)).differentiableAt)]
  rfl

theorem GaussianJet.sum_partial {n : ℕ} {I : Type*} (s : Finset I)
    (f : I → GaussianJet n) (i : Fin n) :
    (GaussianJet.finsetSum s f).partial i=GaussianJet.finsetSum s (fun j => (f j).partial i) := by
  classical
  apply GaussianJet.ext_f
  funext x
  change fderiv ℝ (fun z => ∑ j∈s,(f j).f z) x (Pi.single i 1)=∑ j∈s,((f j).partial i).f x
  rw [fderiv_fun_sum (fun j _ => ((f j).smooth.differentiable (by simp)).differentiableAt)]
  simp only [ContinuousLinearMap.sum_apply,GaussianJet.partial]

noncomputable def gaussianJetProjection {n k : ℕ} (f : Fin k → GaussianJet n)
    (z : Fin k → ℝ) : GaussianJet n :=
  GaussianJet.finsetSum Finset.univ (fun a => (f a).smul (z a))

theorem gaussianJetProjection_apply {n k : ℕ} (f : Fin k → GaussianJet n)
    (z : Fin k → ℝ) (x : Fin n → ℝ) :
    (gaussianJetProjection f z).f x=∑ a,z a*(f a).f x := rfl

theorem gaussianJetProjection_partial {n k : ℕ} (f : Fin k → GaussianJet n)
    (z : Fin k → ℝ) (i : Fin n) :
    (gaussianJetProjection f z).partial i=gaussianJetProjection (fun a => (f a).partial i) z := by
  simp only [gaussianJetProjection,GaussianJet.sum_partial,GaussianJet.smul_partial]

theorem gaussianJetProjection_iteratedPartial {n k : ℕ} (f : Fin k → GaussianJet n)
    (z : Fin k → ℝ) (is : List (Fin n)) :
    (gaussianJetProjection f z).iteratedPartial is=
      gaussianJetProjection (fun a => (f a).iteratedPartial is) z := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [GaussianJet.iteratedPartial,ih,gaussianJetProjection_partial]

theorem gaussianJetProjection_divergence {n k : ℕ} (u : Fin k → Fin n → GaussianJet n)
    (z : Fin k → ℝ) :
    GaussianJet.divergence (fun i => gaussianJetProjection (fun a => u a i) z)=
      gaussianJetProjection (fun a => GaussianJet.divergence (u a)) z := by
  classical
  apply GaussianJet.ext_f
  funext x
  simp only [GaussianJet.divergence_apply,gaussianJetProjection_partial,gaussianJetProjection_apply]
  simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [Finset.sum_comm]

end Asakura.Chapter12
