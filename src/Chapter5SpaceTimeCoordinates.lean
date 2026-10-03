import Chapter5ObservationNoiseMap

open Set
open scoped BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 1800000

noncomputable def spaceTimeCoordinates (d : ℕ) :
    (Fin (d+1) → ℝ) →L[ℝ] ((Fin d → ℝ) × ℝ) :=
  (ContinuousLinearMap.pi (fun i : Fin d => ContinuousLinearMap.proj i.succ)).prod
    (ContinuousLinearMap.proj 0)

theorem spaceTimeCoordinates_cons {d : ℕ} (t : ℝ) (x : Fin d → ℝ) :
    spaceTimeCoordinates d (Fin.cons t x)=(x,t) := by
  ext i <;> simp [spaceTimeCoordinates]

theorem spaceTimeCoordinates_time {d : ℕ} (x : Fin (d+1) → ℝ) :
    (spaceTimeCoordinates d x).2=x 0 := rfl

theorem augmented_noise_gram {d n : ℕ} (Q : Fin n → Fin d → ℝ)
    (i j : Fin (d+1)) :
    (∑ l,(Fin.cons 0 (Q l) : Fin (d+1) → ℝ) i*(Fin.cons 0 (Q l) : Fin (d+1) → ℝ) j)=
      (Fin.cases (fun _ : Fin (d+1) => (0:ℝ))
        (fun k => (Fin.cases (0:ℝ) (fun h => ∑ l,Q l k*Q l h) : Fin (d+1) → ℝ)) :
          Fin (d+1) → Fin (d+1) → ℝ) i j := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp
  · refine Fin.cases ?_ (fun h => ?_) j <;> simp

end Asakura.Chapter5
