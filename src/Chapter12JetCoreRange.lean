import Chapter12ClosedSobolevJets

open Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- No extra smooth functions are introduced by the linear span of jets:
linearity of the scalar core propagates through all derivative orders. -/
theorem jet_span_eq_range {n : ℕ} {ι : Type*} (p : ℝ≥0∞) [Fact (1≤p)]
    (E : Fin (n+1) → Type*) [∀ j,NormedAddCommGroup (E j)] [∀ j,NormedSpace ℝ (E j)]
    (D : ∀ j : Fin n,E j.castSucc →ₗ.[ℝ] E j.succ)
    (jet : ι → PiLp p E)
    (hjet : ∀ c j,(jet c j.castSucc,jet c j.succ)∈(D j).graph)
    (hz : ∃ c,jet c 0=0)
    (ha : ∀ c d,∃ e,jet e 0=jet c 0+jet d 0)
    (hs : ∀ (a : ℝ) c,∃ e,jet e 0=a • jet c 0) :
    (Submodule.span ℝ (range jet) : Set _) = range jet := by
  let V := Submodule.span ℝ (range jet)
  have hV : ∀ x∈V,∀ j : Fin n,(x j.castSucc,x j.succ)∈(D j).graph := by
    intro x hx j
    let L : PiLp p E →L[ℝ] E j.castSucc × E j.succ :=
      (PiLp.proj p E j.castSucc).prod (PiLp.proj p E j.succ)
    have hh : V≤(D j).graph.comap L.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨c,rfl⟩
      exact hjet c j
    exact hh hx
  have hinj := closed_jet_value_injective p E D V hV
  have core (c : ι) : jet c∈V := Submodule.subset_span (mem_range_self c)
  have heq (c : ι) (x : PiLp p E) (hx : x∈V) (he : jet c 0=x 0) : jet c=x :=
    congrArg Subtype.val (hinj (a₁ := ⟨jet c,core c⟩) (a₂ := ⟨x,hx⟩) he)
  apply Set.Subset.antisymm
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      obtain ⟨c,hc⟩ := hz
      exact ⟨c,heq c 0 V.zero_mem hc⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨c,rfl⟩ := ihx
      obtain ⟨d,rfl⟩ := ihy
      obtain ⟨e,he⟩ := ha c d
      exact ⟨e,heq e (jet c+jet d) (V.add_mem hx hy) he⟩
    | smul a x hx ih =>
      obtain ⟨c,rfl⟩ := ih
      obtain ⟨e,he⟩ := hs a c
      exact ⟨e,heq e (a • jet c) (V.smul_mem a hx) he⟩
  · exact Submodule.subset_span

end Asakura.Chapter12
