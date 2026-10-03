import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.SpecificLimits.Normed

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.EndToEnd
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- A finite-valued family of L2 classes has a jointly measurable realization. -/
theorem simple_lp_joint_measurable {E Ω : Type*} [MeasurableSpace E]
    [MeasurableSpace Ω] (P : Measure Ω) (s : SimpleFunc E (Lp ℝ 2 P)) :
    Measurable (fun z : E × Ω => (s z.1 : Ω → ℝ) z.2) := by
  letI : MeasurableSpace (Lp ℝ 2 P) := borel _
  letI : BorelSpace (Lp ℝ 2 P) := ⟨rfl⟩
  letI : Fintype (Set.range s) := s.finite_range.fintype
  have he : Measurable (fun z : (Set.range s) × Ω => (z.1.val : Ω → ℝ) z.2) :=
    measurable_from_prod_countable_right (fun x => (Lp.stronglyMeasurable x.val).measurable)
  have hs : Measurable (fun x : E => (⟨s x,⟨x,rfl⟩⟩ : Set.range s)) := s.measurable.subtype_mk
  exact he.comp ((hs.comp measurable_fst).prodMk measurable_snd)

/-- Strong measurability of a family of L2 equivalence classes is enough to
construct joint representatives, even for a non-countably-generated probability space.
The proof takes measurable, geometrically accurate simple approximations. -/
theorem lp_joint_representative {E Ω : Type*} [MeasurableSpace E]
    [MeasurableSpace Ω] (P : Measure Ω) (Z : E → Lp ℝ 2 P)
    (hZ : StronglyMeasurable Z) :
    ∃ G : E × Ω → ℝ, Measurable G ∧ ∀ x, (Z x : Ω → ℝ) =ᵐ[P] (fun w => G (x,w)) := by
  classical
  letI : MeasurableSpace (Lp ℝ 2 P) := borel _
  letI : BorelSpace (Lp ℝ 2 P) := ⟨rfl⟩
  have hex (n : ℕ) (x : E) : ∃ k, dist (hZ.approx k x) (Z x) < (1/2:ℝ)^n := by
    exact ((Metric.tendsto_nhds.mp (hZ.tendsto_approx x)) _ (by positivity)).exists
  let k := fun n x => Nat.find (hex n x)
  let V := fun n x => hZ.approx (k n x) x
  let g := fun n (z : E × Ω) => (V n z.1 : Ω → ℝ) z.2
  have hgm n : Measurable (g n) := by
    exact Measurable.find
      (fun j => simple_lp_joint_measurable P (hZ.approx j))
      (fun j => (measurableSet_lt (((hZ.approx j).stronglyMeasurable.dist hZ).measurable)
        measurable_const).preimage measurable_fst)
      (fun z : E × Ω => hex n z.1)
  have hv n x : ‖V n x-Z x‖ ≤ (1/2:ℝ)^n := by
    simpa only [dist_eq_norm,V,k] using (Nat.find_spec (hex n x)).le
  let G := fun z => limUnder atTop (fun n => g n z)
  refine ⟨G,(StronglyMeasurable.limUnder (fun n => (hgm n).stronglyMeasurable)).measurable,?_⟩
  intro x
  have hn n : eLpNorm (fun w => g n (x,w)-(Z x : Ω → ℝ) w) 2 P ≤ ENNReal.ofReal ((1/2:ℝ)^n) := by
    change eLpNorm ((V n x : Ω → ℝ) - (Z x : Ω → ℝ)) 2 P ≤ _
    rw [← eLpNorm_congr_ae (Lp.coeFn_sub (V n x) (Z x)),← Lp.enorm_def,← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hv n x)
  have hsum : (∑' n, eLpNorm (fun w => g n (x,w)-(Z x : Ω → ℝ) w) 2 P) ≠ ∞ :=
    (lt_of_le_of_lt (ENNReal.tsum_le_tsum hn)
      ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).tsum_ofReal_lt_top)).ne
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1:ℝ≥0∞) ≤ 2) hsum] with w hw
  have hl : Tendsto (fun n => g n (x,w)) atTop (𝓝 ((Z x : Ω → ℝ) w)) := by
    have hzero := tendsto_zero_iff_norm_tendsto_zero.mpr hw.tendsto_atTop_zero
    simpa only [sub_add_cancel,zero_add] using hzero.add
      (tendsto_const_nhds (x := (Z x : Ω → ℝ) w))
  exact hl.limUnder_eq.symm

#print axioms simple_lp_joint_measurable
#print axioms lp_joint_representative
end Asakura.EndToEnd
