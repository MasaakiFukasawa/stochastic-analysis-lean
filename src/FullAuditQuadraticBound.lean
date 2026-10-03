import FullAuditPartitionEnergy
import FullAuditJensenContraction

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- The essential terminal bound is inherited at every deterministic time
 through the two constant bounds on conditional expectation. -/
theorem conditional_terminal_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {G : MeasurableSpace Ω} (hG : G ≤ m)
    (U Y : Ω → ℝ) (hY : MemLp Y ∞ P) (hU : U =ᵐ[P] P[Y | G]) :
    ∀ᵐ ω ∂P, |U ω| ≤ (eLpNorm Y ∞ P).toReal := by
  let C := (eLpNorm Y ∞ P).toReal
  have hb : ∀ᵐ ω ∂P, |Y ω| ≤ C := by
    have he := eLpNorm_exponent_top hY.aestronglyMeasurable
    filter_upwards [ae_le_eLpNormEssSup (f := Y) (μ := P)] with ω hω
    rw [← he] at hω
    simpa only [toReal_enorm,Real.norm_eq_abs] using ENNReal.toReal_mono hY.eLpNorm_ne_top hω
  have hi := hY.integrable (by simp)
  have hlo := condExp_mono (m := G) (integrable_const (-C)) hi
    (hb.mono fun ω hω => by have h := neg_abs_le (Y ω); linarith)
  have hhi := condExp_mono (m := G) hi (integrable_const C)
    (hb.mono fun ω hω => (le_abs_self _).trans hω)
  filter_upwards [hU,hlo,hhi] with ω hU hlo hhi
  simp only [condExp_const hG] at hlo hhi
  rw [hU]
  exact abs_le.mpr ⟨hlo,hhi⟩

/-- The full squared-norm estimate in the manuscript. The proof applies the
 partition-square lemma to Y itself, computes ΔY=2XΔX, and uses the actual
 conditional terminal bound to obtain the constant 4. -/
theorem bounded_partition_square_estimate {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ι → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t)) (hTop : ∀ t, MemLp (X t) ∞ P)
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (hz : X ⊥ =ᵐ[P] 0) (π : ℕ → ι) (hπ : Monotone π) (h0 : π 0 = ⊥) (N : ℕ) (hN : π N = ⊤) :
    (∫ ω, (X ⊤ ω ^ 2-partitionSquares X π N ⊤ ω)^2 ∂P) ≤
      4 * (eLpNorm (X ⊤) ∞ P).toReal^2 * (∫ ω, X ⊤ ω ^ 2 ∂P) := by
  let Y := fun t ω => X t ω ^ 2-partitionSquares X π N t ω
  let C := (eLpNorm (X ⊤) ∞ P).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have h2 (t : ι) : MemLp (X t) 2 P := (hTop t).mono_exponent (by simp)
  have hYtop (t : ι) : MemLp (Y t) ∞ P := partition_defect_memLp_top P X hTop π N t
  have hY2 (t : ι) : MemLp (Y t) 2 P := (hYtop t).mono_exponent (by simp)
  have hYm (t : ι) : Measurable[F t] (Y t) :=
    (partition_square_defect_adapted_integrable P F hF X hm h2 π N t).1
  have hYmart (s t : ι) (hst : s ≤ t) : P[Y t | F s] =ᵐ[P] Y s :=
    partition_square_martingale_written P F hF hle X hm h2 hmart π hπ h0 N hN s t hst
  have hYzero : Y ⊥ =ᵐ[P] 0 := by
    filter_upwards [hz] with ω hω
    simp [Y,partition_squares_initial,hω]
  have hEX := partition_square_energy_written P F hF hle X hm h2 hmart hz π hπ h0 N hN
  have hEY := partition_square_energy_written P F hF hle Y hYm hY2 hYmart hYzero π hπ h0 N hN
  have hbound (t : ι) : ∀ᵐ ω ∂P, |X t ω| ≤ C :=
    conditional_terminal_bound P (hle t) (X t) (X ⊤) (hTop ⊤) (hmart t ⊤ le_top).symm
  have hpoint : ∀ᵐ ω ∂P, partitionSquares Y π N ⊤ ω ≤ 4*C^2*partitionSquares X π N ⊤ ω := by
    filter_upwards [ae_all_iff.mpr (fun j => hbound (π j))] with ω hω
    simp only [partitionSquares,min_eq_right le_top]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have he := square_defect_partition_increment X π hπ N j (Finset.mem_range.mp hj) ω
    change (Y (π (j+1)) ω-Y (π j) ω)^2 ≤ 4*C^2*(X (π (j+1)) ω-X (π j) ω)^2
    rw [show Y (π (j+1)) ω-Y (π j) ω = 2*X (π j) ω*(X (π (j+1)) ω-X (π j) ω) from he]
    have hx : X (π j) ω ^ 2 ≤ C^2 := by nlinarith [sq_abs (X (π j) ω),abs_nonneg (X (π j) ω),hω j]
    have hb := mul_le_mul_of_nonneg_right hx (sq_nonneg (X (π (j+1)) ω-X (π j) ω))
    nlinarith
  have h := integral_mono_ae (partition_squares_integrable P Y hY2 π N ⊤)
    ((partition_squares_integrable P X h2 π N ⊤).const_mul (4*C^2)) hpoint
  rw [integral_const_mul,hEX,hEY] at h
  exact h

/-- Taking square roots produces the exact displayed factor 2. -/
theorem bounded_partition_square_norm {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ι → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t)) (hTop : ∀ t, MemLp (X t) ∞ P)
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (hz : X ⊥ =ᵐ[P] 0) (π : ℕ → ι) (hπ : Monotone π) (h0 : π 0 = ⊥) (N : ℕ) (hN : π N = ⊤) :
    Real.sqrt (∫ ω, (X ⊤ ω ^ 2-partitionSquares X π N ⊤ ω)^2 ∂P) ≤
      2 * (eLpNorm (X ⊤) ∞ P).toReal * Real.sqrt (∫ ω, X ⊤ ω ^ 2 ∂P) := by
  have h := bounded_partition_square_estimate P F hF hle X hm hTop hmart hz π hπ h0 N hN
  have hL : 0 ≤ ∫ ω, (X ⊤ ω ^ 2-partitionSquares X π N ⊤ ω)^2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hR : 0 ≤ ∫ ω, X ⊤ ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hC : 0 ≤ (eLpNorm (X ⊤) ∞ P).toReal := ENNReal.toReal_nonneg
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt hL,mul_pow,mul_pow,Real.sq_sqrt hR]
  norm_num only [show (2 : ℝ)^2 = 4 by norm_num]
  exact h

end Asakura.FullAudit
