import FullAuditMartingaleCrossIncrement

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- The exact finite telescoping identity for the printed partition squares. -/
theorem finite_square_cross_identity (x : ℕ → ℝ) (N : ℕ) :
    x N ^ 2 - ∑ j ∈ Finset.range N, (x (j+1)-x j)^2 =
      x 0 ^ 2 + 2 * ∑ j ∈ Finset.range N, x j * (x (j+1)-x j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    nlinarith [ih]

noncomputable def partitionSquares {Ω ι : Type*} [LinearOrder ι]
    (X : ι → Ω → ℝ) (π : ℕ → ι) (N : ℕ) (t : ι) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.range N, (X (min t (π (j+1))) ω-X (min t (π j)) ω)^2

theorem partition_squares_integrable {Ω ι : Type*} [MeasurableSpace Ω] [LinearOrder ι]
    (P : Measure Ω) (X : ι → Ω → ℝ) (h2 : ∀ t, MemLp (X t) 2 P)
    (π : ℕ → ι) (N : ℕ) (t : ι) : Integrable (partitionSquares X π N t) P := by
  apply integrable_finset_sum
  intro j hj
  have hd := (h2 (min t (π (j+1)))).sub (h2 (min t (π j)))
  exact (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mp hd

/-- The unbounded L2 partition-square lemma, connected to the actual martingale
 and the original arbitrary finite partition. The before/inside/after interval
 cases are checked in cross_increment_martingale. -/
theorem partition_square_martingale_written {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ι → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t)) (h2 : ∀ t, MemLp (X t) 2 P)
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (π : ℕ → ι) (hπ : Monotone π) (h0 : π 0 = ⊥) (N : ℕ) (hN : π N = ⊤)
    (s t : ι) (hst : s ≤ t) :
    P[(fun ω => X t ω ^ 2-partitionSquares X π N t ω) | F s] =ᵐ[P]
      (fun ω => X s ω ^ 2-partitionSquares X π N s ω) := by
  let S : ι → Ω → ℝ := fun u => ∑ j ∈ Finset.range N, crossIncrement X (π j) (π (j+1)) u
  have hi (u : ι) (j : ℕ) : Integrable (crossIncrement X (π j) (π (j+1)) u) P :=
    l2_product_increment_integrable P (h2 _) (h2 _)
  have hSi (u : ι) : Integrable (S u) P := by
    exact integrable_finsetSum' (Finset.range N) (fun j _ => hi u j)
  have hS : P[S t | F s] =ᵐ[P] S s := by
    have hs := condExp_finsetSum (fun j (_ : j ∈ Finset.range N) => hi t j) (F s)
    have hc := ae_all_iff.mpr (fun j => cross_increment_martingale P F hF hle X hm h2 hmart
      (π j) (π (j+1)) (hπ (Nat.le_succ j)) s t hst)
    filter_upwards [hs,hc] with ω hs hc
    change P[S t | F s] ω = S s ω
    rw [hs]
    simp only [S,Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => hc j
  have hid (u : ι) : (fun ω => X u ω ^ 2-partitionSquares X π N u ω) =
      (fun ω => X ⊥ ω ^ 2) + (2 : ℝ) • S u := by
    funext ω
    have h := finite_square_cross_identity (fun j => X (min u (π j)) ω) N
    simpa only [h0,hN,min_eq_left le_top,min_eq_right bot_le,S,partitionSquares,crossIncrement,Finset.sum_apply,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,Pi.sub_apply] using h
  have hbase : Integrable (fun ω => X ⊥ ω ^ 2) P :=
    (memLp_two_iff_integrable_sq (h2 ⊥).aestronglyMeasurable).mp (h2 ⊥)
  have hbaseCE : P[(fun ω => X ⊥ ω ^ 2) | F s] = fun ω => X ⊥ ω ^ 2 :=
    condExp_of_stronglyMeasurable (hle s) (((hm ⊥).mono (hF bot_le) le_rfl).pow_const 2).stronglyMeasurable hbase
  rw [hid t,hid s]
  have hadd := condExp_add hbase ((hSi t).smul (2 : ℝ)) (F s)
  have hmul := condExp_smul (2 : ℝ) (S t) (F s) (μ := P)
  filter_upwards [hadd,hmul,hS] with ω ha hm hs
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hbaseCE] at ha hm ⊢
  rw [ha,hm,hs]

/-- Adaptedness and L1 membership of the actual square-defect process. -/
theorem partition_square_defect_adapted_integrable {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] (P : Measure Ω)
    (F : ι → MeasurableSpace Ω) (hF : Monotone F)
    (X : ι → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t)) (h2 : ∀ t, MemLp (X t) 2 P)
    (π : ℕ → ι) (N : ℕ) (t : ι) :
    Measurable[F t] (fun ω => X t ω ^ 2-partitionSquares X π N t ω) ∧
    Integrable (fun ω => X t ω ^ 2-partitionSquares X π N t ω) P := by
  constructor
  · apply ((hm t).pow_const 2).sub
    apply Finset.measurable_sum
    intro j hj
    exact (((hm _).mono (hF (min_le_left _ _)) le_rfl).sub
      ((hm _).mono (hF (min_le_left _ _)) le_rfl)).pow_const 2
  · exact ((memLp_two_iff_integrable_sq (h2 t).aestronglyMeasurable).mp (h2 t)).sub
      (partition_squares_integrable P X h2 π N t)

/-- The finite formula preserves continuous paths, as required by M1. -/
theorem partition_square_defect_continuous {Ω ι : Type*} [LinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] (X : ι → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => X t ω)) (π : ℕ → ι) (N : ℕ) (ω : Ω) :
    Continuous (fun t => X t ω ^ 2-partitionSquares X π N t ω) := by
  apply ((hc ω).pow 2).sub
  apply continuous_finset_sum
  intro j hj
  exact (((hc ω).comp (continuous_id.min continuous_const)).sub
    ((hc ω).comp (continuous_id.min continuous_const))).pow 2

end Asakura.FullAudit
