import Chapter1WrittenStoppedMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/- Asano: localize measurability using prop:st3, apply the ordinary tower property,
then split into the two comparison events. No stopped conditional-expectation
identity from the library is used. -/
open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter1Written
variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The local measurability calculation printed in Asano 1), also valid for 2). -/
theorem written_localized_stopped_measurable {ι : Type*} [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (τ σ : Ω → ι)
    (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    (hσ : ∀ i, MeasurableSet[F i] {ω | σ ω ≤ i})
    {E : Set Ω}
    (hE : MeasurableSet[writtenStoppedSpace m F τ hτ ⊓ writtenStoppedSpace m F σ hσ] E)
    (horder : ∀ ω ∈ E, τ ω ≤ σ ω) {Y : Ω → ℝ}
    (hY : Measurable[writtenStoppedSpace m F τ hτ] Y) :
    Measurable[writtenStoppedSpace m F τ hτ ⊓ writtenStoppedSpace m F σ hσ] (E.indicator Y) := by
  classical
  let T := writtenStoppedSpace m F τ hτ
  let S := writtenStoppedSpace m F σ hσ
  have hTm : T ≤ m := fun A hA => hA.1
  have hmY : Measurable[m] Y := hY.mono hTm le_rfl
  have hEm : MeasurableSet[m] E := hE.1.1
  have hmin := (written_stopping_min_max F τ σ hτ hσ).1
  have hEq := written_stopped_min_sigma m F τ σ hτ hσ
  rw [← hEq]
  apply (stopped_measurable_iff_written m F (fun ω => min (τ ω) (σ ω)) hmin
    (E.indicator Y) (hmY.indicator hEm)).mpr
  intro i
  have hloc := (stopped_measurable_iff_written m F τ hτ Y hmY).mp hY i
  have hEi : MeasurableSet[F i] (E ∩ {ω | min (τ ω) (σ ω) ≤ i}) := by
    have hE' := hE
    rw [← hEq] at hE'
    exact hE'.2 i
  have hid : {ω | min (τ ω) (σ ω) ≤ i}.indicator (E.indicator Y) =
      (E ∩ {ω | min (τ ω) (σ ω) ≤ i}).indicator ({ω | τ ω ≤ i}.indicator Y) := by
    funext ω
    by_cases he : ω ∈ E
    · have hle := horder ω he
      by_cases hi : τ ω ≤ i
      · simp [Set.indicator, he, hi]
      · have hsi : ¬ σ ω ≤ i := fun h => hi (hle.trans h)
        simp [Set.indicator, he, hi, hsi]
    · simp [Set.indicator, he]
  rw [hid]
  exact hloc.indicator hEi

/-- Once localized measurability is proved, the tower property gives Asano's identity. -/
theorem written_asano_event {ι : Type*} [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (τ σ : Ω → ι)
    (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    (hσ : ∀ i, MeasurableSet[F i] {ω | σ ω ≤ i})
    {E : Set Ω}
    (hE : MeasurableSet[writtenStoppedSpace m F τ hτ ⊓ writtenStoppedSpace m F σ hσ] E)
    (horder : ∀ ω ∈ E, τ ω ≤ σ ω) {X : Ω → ℝ} (hX : Integrable X P) :
    P[E.indicator X | writtenStoppedSpace m F τ hτ] =ᵐ[P]
      E.indicator (P[X | writtenStoppedSpace m F τ hτ ⊓ writtenStoppedSpace m F σ hσ]) := by
  let T := writtenStoppedSpace m F τ hτ
  let S := writtenStoppedSpace m F σ hσ
  let M := T ⊓ S
  have hTm : T ≤ m := fun A hA => hA.1
  have hMm : M ≤ m := le_trans inf_le_left hTm
  have hEm : MeasurableSet[m] E := hE.1.1
  have hz := written_localized_stopped_measurable F τ σ hτ hσ hE horder
    (stronglyMeasurable_condExp (μ := P) (f := X) (m := T)).measurable
  have hzi : Integrable (E.indicator (P[X | T])) P := integrable_condExp.indicator hEm
  have hfirst := condExp_indicator (m := T) hX hE.1
  have htower := condExp_condExp_of_le (show M ≤ T from inf_le_left) hTm
    (μ := P) (f := E.indicator X)
  have hcond := condExp_congr_ae (m := M) hfirst
  have hself : P[E.indicator (P[X | T]) | M] = E.indicator (P[X | T]) :=
    condExp_of_stronglyMeasurable hMm hz.stronglyMeasurable hzi
  have hlast := condExp_indicator (m := M) hX hE
  rw [hself] at hcond
  exact hfirst.trans (hcond.symm.trans (htower.trans hlast))

/-- Asano 1) and 2), with the manuscript's extended-real index set. -/
theorem written_asano_indicators (Λ : Set EReal)
    (F : Λ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ i, F i ≤ m)
    (τ σ : Ω → Λ)
    (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    (hσ : ∀ i, MeasurableSet[F i] {ω | σ ω ≤ i})
    {X : Ω → ℝ} (hX : Integrable X P) :
    (P[({ω | τ ω < σ ω}).indicator X | writtenStoppedSpace m F τ hτ] =ᵐ[P]
      ({ω | τ ω < σ ω}).indicator
        (P[X | writtenStoppedSpace m F τ hτ ⊓ writtenStoppedSpace m F σ hσ])) ∧
    (P[({ω | τ ω ≤ σ ω}).indicator X | writtenStoppedSpace m F τ hτ] =ᵐ[P]
      ({ω | τ ω ≤ σ ω}).indicator
        (P[X | writtenStoppedSpace m F τ hτ ⊓ writtenStoppedSpace m F σ hσ])) := by
  have hc := written_extended_comparison m Λ F hF hle τ σ hτ hσ
  exact ⟨written_asano_event F τ σ hτ hσ hc.1 (fun _ h => h.le) hX,
    written_asano_event F τ σ hτ hσ hc.2 (fun _ h => h) hX⟩

/-- Asano 3): the displayed calculation, split into {τ≤σ} and its complement. -/
theorem written_asano_commute (Λ : Set EReal)
    (F : Λ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ i, F i ≤ m)
    (τ σ : Ω → Λ)
    (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i})
    (hσ : ∀ i, MeasurableSet[F i] {ω | σ ω ≤ i})
    {X : Ω → ℝ} (hX : Integrable X P) :
    P[P[X | writtenStoppedSpace m F σ hσ] | writtenStoppedSpace m F τ hτ] =ᵐ[P]
      P[X | writtenStoppedSpace m F τ hτ ⊓ writtenStoppedSpace m F σ hσ] := by
  classical
  let T := writtenStoppedSpace m F τ hτ
  let S := writtenStoppedSpace m F σ hσ
  let M := T ⊓ S
  let E : Set Ω := {ω | τ ω ≤ σ ω}
  have hE : MeasurableSet[M] E := (written_extended_comparison m Λ F hF hle τ σ hτ hσ).2
  have hTm : T ≤ m := fun A hA => hA.1
  have hSm : S ≤ m := fun A hA => hA.1
  have hEm : MeasurableSet[m] E := hE.1.1
  have hET : MeasurableSet[T] E := hE.1
  have hES : MeasurableSet[S] E := hE.2
  have hcomp : MeasurableSet[S ⊓ T] Eᶜ := by
    rw [inf_comm]
    exact hE.compl
  have hleft := written_asano_event (P := P) F τ σ hτ hσ hE (fun _ h => h)
    (integrable_condExp (f := X) (m := S))
  have htower : P[P[X | S] | M] =ᵐ[P] P[X | M] :=
    condExp_condExp_of_le (show M ≤ S from inf_le_right) hSm
  have hleft' : P[E.indicator (P[X | S]) | T] =ᵐ[P] E.indicator (P[X | M]) := by
    filter_upwards [hleft, htower] with ω hl ht
    change P[E.indicator (P[X | S]) | T] ω = E.indicator (P[P[X | S] | M]) ω at hl
    rw [hl]
    by_cases he : ω ∈ E <;> simp [Set.indicator, he, ht]
  have hright := written_asano_event (P := P) F σ τ hσ hτ hcomp
    (fun ω h => (not_le.mp (show ¬ τ ω ≤ σ ω from h)).le) hX
  have hi := condExp_indicator (m := S) hX hES.compl
  have hreplace : Eᶜ.indicator (P[X | S]) =ᵐ[P] Eᶜ.indicator (P[X | M]) := by
    have hr := hi.symm.trans hright
    simpa only [inf_comm] using hr
  have hrc := condExp_congr_ae (m := T) hreplace
  have hrself : P[Eᶜ.indicator (P[X | M]) | T] = Eᶜ.indicator (P[X | M]) :=
    condExp_of_stronglyMeasurable hTm
      ((stronglyMeasurable_condExp (μ := P) (f := X) (m := M)).mono inf_le_left |>.indicator hET.compl)
      (integrable_condExp.indicator hEm.compl)
  rw [hrself] at hrc
  have hsplit (Y : Ω → ℝ) : E.indicator Y + Eᶜ.indicator Y = Y := by
    funext ω
    by_cases h : ω ∈ E <;> simp [Set.indicator, h]
  have hadd := condExp_add
    ((integrable_condExp (μ := P) (f := X) (m := S)).indicator hEm)
    ((integrable_condExp (μ := P) (f := X) (m := S)).indicator hEm.compl) T
  rw [hsplit] at hadd
  filter_upwards [hadd, hleft', hrc] with ω ha hl hr
  change P[P[X | S] | T] ω = P[X | M] ω
  rw [ha]
  change P[E.indicator (P[X | S]) | T] ω + P[Eᶜ.indicator (P[X | S]) | T] ω = _
  rw [hl, hr]
  exact congrFun (hsplit (P[X | M])) ω

end Asakura.Chapter1Written
