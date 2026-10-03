import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Extension by zero is an isometry from the restricted-measure L2 space.
This embeds a finite time horizon into the Wiener space on the half-line. -/
noncomputable def L2ZeroExtension {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) : Lp E 2 (μ.restrict s) →ₗᵢ[ℝ] Lp E 2 μ := by
  let hi (f : Lp E 2 (μ.restrict s)) : MemLp (s.indicator (f : α → E)) 2 μ :=
    (memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)
  let J := fun f : Lp E 2 (μ.restrict s) => (hi f).toLp _
  have hj (f : Lp E 2 (μ.restrict s)) : (J f : α → E) =ᵐ[μ] s.indicator (f : α → E) :=
    (hi f).coeFn_toLp
  refine { toLinearMap := { toFun := J, map_add' := ?_,map_smul' := ?_ },norm_map' := ?_ }
  · intro f g
    apply Lp.ext
    have hfg := (ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_add f g)
    filter_upwards [hj (f+g),hj f,hj g,Lp.coeFn_add (J f) (J g),hfg] with x h1 h2 h3 h4 h5
    rw [h1,h4]
    simp only [Pi.add_apply]
    rw [h2,h3,h5]
    exact congrFun (Set.indicator_add' s (f : α → E) g) x
  · intro a f
    apply Lp.ext
    have haf := (ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_smul a f)
    filter_upwards [hj (a • f),hj f,Lp.coeFn_smul a (J f),haf] with x h1 h2 h3 h4
    change J (a • f) x = (a • J f) x
    rw [h1,h3]
    simp only [Pi.smul_apply]
    rw [h2,h4]
    by_cases hx : x ∈ s <;> simp [Set.indicator,hx]
  · intro f
    change ‖(hi f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp,eLpNorm_indicator_eq_eLpNorm_restrict hs]
    exact (Lp.norm_def f).symm

theorem L2ZeroExtension_coe {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) (f : Lp E 2 (μ.restrict s)) :
    (L2ZeroExtension μ s hs f : α → E) =ᵐ[μ] s.indicator (f : α → E) :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).coeFn_toLp

end Asakura.Chapter12
