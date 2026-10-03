import FullAuditNoncommutingCE

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.FullAudit

/-- On a discrete range, a generated sigma algebra consists exactly of unions of fibers. -/
theorem fiber_sigma_eq_comap {Ω β : Type*} [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (q : Ω → β) : fiberSigma q = MeasurableSpace.comap q inferInstance := by
  apply le_antisymm
  · intro A hA
    refine ⟨q '' A,MeasurableSet.of_discrete,?_⟩
    ext ω
    constructor
    · rintro ⟨z,hz,hq⟩
      exact (hA z ω hq).mp hz
    · intro hω
      exact ⟨ω,hω,rfl⟩
  · rintro A ⟨B,hB,rfl⟩ x y hxy
    simp only [mem_preimage,hxy]

noncomputable def diceLaw : Measure (Fin 6) := (PMF.uniformOfFintype (Fin 6)).toMeasure
instance : IsProbabilityMeasure diceLaw := by unfold diceLaw; infer_instance

def diceParity (i : Fin 6) : ℕ := (i.val+1)%2
def diceValue (i : Fin 6) : ℝ := (i.val : ℝ)+1
def diceEstimate (i : Fin 6) : ℝ := if diceParity i = 1 then 3 else 4

theorem dice_integral (f : Fin 6 → ℝ) :
    (∫ i, f i ∂diceLaw) = (f 0+f 1+f 2+f 3+f 4+f 5)/6 := by
  simp [diceLaw,PMF.integral_eq_sum,PMF.uniformOfFintype_apply,Fin.sum_univ_succ,smul_eq_mul]
  ring

/-- There are four events: empty, the odd faces, the even faces, and all faces. -/
theorem dice_generated_events (A : Set (Fin 6)) :
    MeasurableSet[MeasurableSpace.comap diceParity inferInstance] A ↔
      A = ∅ ∨ A = {i | diceParity i = 1} ∨ A = {i | diceParity i = 0} ∨ A = univ := by
  rw [← fiber_sigma_eq_comap]
  constructor
  · intro hA
    have h02 := hA 0 2 (by decide)
    have h04 := hA 0 4 (by decide)
    have h13 := hA 1 3 (by decide)
    have h15 := hA 1 5 (by decide)
    by_cases h0 : (0 : Fin 6) ∈ A <;> by_cases h1 : (1 : Fin 6) ∈ A
    · right; right; right
      ext i; fin_cases i <;> simp_all
    · right; left
      ext i; fin_cases i <;> simp_all [diceParity]
    · right; right; left
      ext i; fin_cases i <;> simp_all [diceParity]
    · left
      ext i; fin_cases i <;> simp_all
  · intro h
    rcases h with rfl|rfl|rfl|rfl
    · intro x y hxy; rfl
    · intro x y hxy
      simp only [mem_setOf_eq,hxy]
    · intro x y hxy
      simp only [mem_setOf_eq,hxy]
    · intro x y hxy; rfl

/-- C2 computes 3 on odd faces and 4 on even faces, in the actual uniform law. -/
theorem dice_conditional_expectation :
    diceLaw[diceValue | MeasurableSpace.comap diceParity inferInstance] =ᵐ[diceLaw] diceEstimate := by
  rw [← fiber_sigma_eq_comap]
  have hZ : Measurable[fiberSigma diceParity] diceEstimate := by
    intro B hB x y hxy
    simp only [mem_preimage,diceEstimate,hxy]
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (show fiberSigma diceParity ≤ ⊤ from le_top)
    (show Integrable diceValue diceLaw from .of_finite)
    (fun _ _ _ => (show Integrable diceEstimate diceLaw from .of_finite).integrableOn) _
    hZ.stronglyMeasurable.aestronglyMeasurable
  intro A hA _
  have h02 := hA 0 2 (by decide)
  have h04 := hA 0 4 (by decide)
  have h13 := hA 1 3 (by decide)
  have h15 := hA 1 5 (by decide)
  rw [← integral_indicator (MeasurableSet.of_discrete (s := A)),
    ← integral_indicator (MeasurableSet.of_discrete (s := A)),dice_integral,dice_integral]
  by_cases h0 : (0 : Fin 6) ∈ A <;> by_cases h1 : (1 : Fin 6) ∈ A <;>
    simp_all [Set.indicator,diceValue,diceEstimate,diceParity] <;> norm_num
end Asakura.FullAudit
