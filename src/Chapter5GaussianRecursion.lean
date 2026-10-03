import Chapter5SmoothCylinderData

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter5
set_option maxHeartbeats 2200000

/-- Backwards recursion can keep the full observation vector: coordinates
are stopped at their observation times, so no change of dimension is needed. -/
noncomputable def gaussianRecursion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (u : SmoothCylinderData E) (n : ℕ)
    (Q : ℕ → (Fin (n+1) → ℝ) →L[ℝ] E) (t : ℕ → ℝ) : ℕ → SmoothCylinderData E
  | 0 => u
  | j+1 => (gaussianRecursion u n Q t j).gaussianAverage n (Q j) (t j)

theorem gaussianRecursion_value_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (u : SmoothCylinderData E) (n : ℕ)
    (Q : ℕ → (Fin (n+1) → ℝ) →L[ℝ] E) (t : ℕ → ℝ) (j : ℕ) (x : E) :
    (gaussianRecursion u n Q t (j+1)).value x=
      ∫ z,(gaussianRecursion u n Q t j).value (x+Real.sqrt (t j) • z)
        ∂(Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)).map (Q j) := rfl

theorem gaussianRecursion_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (u : SmoothCylinderData E) (n : ℕ)
    (Q : ℕ → (Fin (n+1) → ℝ) →L[ℝ] E) (t : ℕ → ℝ) (j : ℕ) :
    (gaussianRecursion u n Q t j).firstBound=u.firstBound ∧
      (gaussianRecursion u n Q t j).secondBound=u.secondBound := by
  induction j with
  | zero => exact ⟨rfl,rfl⟩
  | succ j ih => exact ih

end Asakura.Chapter5
