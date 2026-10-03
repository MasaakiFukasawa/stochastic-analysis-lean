import KolmogorovConstruction
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Asakura

/-- Extended-valued Holder seminorm; diagonal terms are zero. -/
noncomputable def holderSup {T E : Type*} [MetricSpace T] [PseudoMetricSpace E]
    (f : T → E) (α : ℝ) : ℝ≥0∞ :=
  ⨆ s, ⨆ t, ENNReal.ofReal (dist (f s) (f t) / (dist s t)^α)

theorem holderSup_le_of_bound {T E : Type*} [MetricSpace T] [PseudoMetricSpace E]
    (f : T → E) (α C : ℝ) (hα : 0 < α) (hC : 0 ≤ C)
    (h : ∀ s t, dist (f s) (f t) ≤ C * (dist s t)^α) :
    holderSup f α ≤ ENNReal.ofReal C := by
  apply iSup_le
  intro s
  apply iSup_le
  intro t
  apply ENNReal.ofReal_le_ofReal
  by_cases hst : s = t
  · subst t; simpa using hC
  · exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hst) α)).mpr (h s t)

theorem bound_of_holderSup_le {T E : Type*} [MetricSpace T] [PseudoMetricSpace E]
    (f : T → E) (α C : ℝ) (hC : 0 ≤ C)
    (h : holderSup f α ≤ ENNReal.ofReal C) :
    ∀ s t, dist (f s) (f t) ≤ C * (dist s t)^α := by
  intro s t
  by_cases hst : s = t
  · subst t; simp; positivity
  have hle : ENNReal.ofReal (dist (f s) (f t) / (dist s t)^α) ≤ ENNReal.ofReal C :=
    calc
      _ ≤ ⨆ v : T, ENNReal.ofReal (dist (f s) (f v) / (dist s v)^α) :=
        le_iSup (fun v : T => ENNReal.ofReal (dist (f s) (f v) / (dist s v)^α)) t
      _ ≤ holderSup f α := le_iSup
        (fun u : T => ⨆ v : T, ENNReal.ofReal (dist (f u) (f v) / (dist u v)^α)) s
      _ ≤ _ := h
  have hr : dist (f s) (f t) / (dist s t)^α ≤ C :=
    (ENNReal.ofReal_le_ofReal_iff hC).mp hle
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hst) α)).mp hr

/-- C.2: the supremum over all cube points equals the countable dense supremum. -/
theorem holderSup_eq_dense {T E : Type*} [MetricSpace T] [PseudoMetricSpace E]
    (D : Set T) (hd : Dense D) (f : T → E) (hf : Continuous f)
    (α : ℝ) (hα : 0 < α) :
    holderSup f α = holderSup (fun t : D => f t) α := by
  have hge : holderSup (fun t : D => f t) α ≤ holderSup f α := by
    apply iSup_le
    intro s
    apply iSup_le
    intro t
    exact le_iSup_of_le s.val (le_iSup_of_le t.val le_rfl)
  apply le_antisymm _ hge
  by_cases htop : holderSup (fun t : D => f t) α = ∞
  · rw [htop]; exact le_top
  let C := (holderSup (fun t : D => f t) α).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hD : holderSup (fun t : D => f t) α ≤ ENNReal.ofReal C := by
    rw [ENNReal.ofReal_toReal htop]
  have hb := bound_of_holderSup_le (fun t : D => f t) α C hC hD
  have hall := holder_bound_from_dense D hd f hf C α hα.le
    (fun s hs t ht => hb ⟨s,hs⟩ ⟨t,ht⟩)
  have hh := holderSup_le_of_bound f α C hα hC hall
  rwa [ENNReal.ofReal_toReal htop] at hh

/-- Continuity of paths reduces an uncountable random supremum to a measurable
countable supremum; no completeness of the probability space is assumed. -/
theorem holderSup_process_measurable {T Ω : Type*} [MetricSpace T] [MeasurableSpace Ω]
    (D : Set T) (hd : Dense D) (hcount : D.Countable)
    (X : T → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (hcont : ∀ ω, Continuous (fun t => X t ω)) (α : ℝ) (hα : 0 < α) :
    Measurable (fun ω => holderSup (fun t => X t ω) α) := by
  let : Countable D := hcount.to_subtype
  have heq : (fun ω => holderSup (fun t => X t ω) α) =
      fun ω => holderSup (fun t : D => X t ω) α := by
    funext ω
    exact holderSup_eq_dense D hd _ (hcont ω) α hα
  rw [heq]
  apply Measurable.iSup
  intro s
  apply Measurable.iSup
  intro t
  exact ((hX s).dist (hX t)).div_const _ |>.ennreal_ofReal
end Asakura
