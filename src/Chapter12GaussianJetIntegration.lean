import Chapter12GaussianJetProducts

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem GaussianJet.integrable {n : ℕ} (f : GaussianJet n) :
    Integrable f.f (Measure.pi fun _ => gaussianReal 0 1) :=
  memLp_one_iff_integrable.mp (f.all_moments 1 (by simp))

noncomputable def GaussianJet.listSum {n : ℕ} : List (GaussianJet n) → GaussianJet n
  | [] => GaussianJet.zero n
  | f::fs => f.add (GaussianJet.listSum fs)

@[simp] theorem GaussianJet.listSum_apply {n : ℕ} (fs : List (GaussianJet n)) (x : Fin n → ℝ) :
    (GaussianJet.listSum fs).f x=(fs.map (fun f => f.f x)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simpa only [GaussianJet.listSum,GaussianJet.add,List.map_cons,List.sum_cons] using congrArg (fun a => f.f x+a) ih

theorem GaussianJet.integral_listSum {n : ℕ} (fs : List (GaussianJet n)) :
    (∫ x,(GaussianJet.listSum fs).f x ∂Measure.pi fun _ => gaussianReal 0 1)=
      (fs.map (fun f => ∫ x,f.f x ∂Measure.pi fun _ => gaussianReal 0 1)).sum := by
  induction fs with
  | nil => simp [GaussianJet.listSum,GaussianJet.zero]
  | cons f fs ih =>
    change (∫ x,f.f x+(GaussianJet.listSum fs).f x ∂Measure.pi fun _ => gaussianReal 0 1)=_
    rw [integral_add f.integrable (GaussianJet.listSum fs).integrable,ih]
    rfl

end Asakura.Chapter12
