import Chapter5EnergyEstimates
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
namespace Asakura.Chapter5

/-- Taking expectations in the energy inequality, with every required
integrability condition explicit. The zero-mean noise is established by
Chapter5EnergyNoise for the actual local martingale. -/
theorem expected_energy_absorption {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U A B R D N : Ω → ℝ)
    (iU : Integrable U P) (iA : Integrable A P) (iB : Integrable B P)
    (iR : Integrable R P) (iD : Integrable D P) (iN : Integrable N P)
    (hU : ∀ᵐ ω ∂P, 0 ≤ U ω) (hA : ∀ᵐ ω ∂P, 0 ≤ A ω)
    (hB : ∀ᵐ ω ∂P, 0 ≤ B ω) (hN : (∫ ω, N ω ∂P) = 0)
    (C l m beta : ℝ) (hC : 0 ≤ C) (hl : C < l) (hm : 0 < m)
    (hb : C*(2+l)+m ≤ beta)
    (he : ∀ᵐ ω ∂P, U ω+beta*A ω+B ω ≤
      R ω+(2*C+C*l+m)*A ω+(C/l)*B ω+D ω/m-N ω) :
    (∫ ω, U ω ∂P) ≤ (∫ ω, R ω ∂P)+(∫ ω, D ω ∂P)/m ∧
    (∫ ω, B ω ∂P) ≤ l/(l-C)*((∫ ω, R ω ∂P)+(∫ ω, D ω ∂P)/m) := by
  have hh := integral_mono_ae ((iU.add (iA.const_mul beta)).add iB)
    ((((iR.add (iA.const_mul (2*C+C*l+m))).add (iB.const_mul (C/l))).add (iD.div_const m)).sub iN) he
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  have hleft : (∫ ω, U ω+beta*A ω+B ω ∂P) =
      (∫ ω, U ω ∂P)+beta*(∫ ω, A ω ∂P)+(∫ ω, B ω ∂P) := by
    rw [integral_add (f := fun ω => U ω+beta*A ω) (g := B) (iU.add (iA.const_mul beta)) iB,
      integral_add iU (iA.const_mul beta),integral_const_mul]
  have hright : (∫ ω, R ω+(2*C+C*l+m)*A ω+(C/l)*B ω+D ω/m-N ω ∂P) =
      (∫ ω, R ω ∂P)+(2*C+C*l+m)*(∫ ω, A ω ∂P)+
        (C/l)*(∫ ω, B ω ∂P)+(∫ ω, D ω ∂P)/m := by
    rw [integral_sub (f := fun ω => R ω+(2*C+C*l+m)*A ω+(C/l)*B ω+D ω/m) (g := N)
      (((iR.add (iA.const_mul (2*C+C*l+m))).add (iB.const_mul (C/l))).add (iD.div_const m)) iN,
      integral_add (f := fun ω => R ω+(2*C+C*l+m)*A ω+(C/l)*B ω) (g := fun ω => D ω/m)
        ((iR.add (iA.const_mul (2*C+C*l+m))).add (iB.const_mul (C/l))) (iD.div_const m),
      integral_add (f := fun ω => R ω+(2*C+C*l+m)*A ω) (g := fun ω => (C/l)*B ω)
        (iR.add (iA.const_mul (2*C+C*l+m))) (iB.const_mul (C/l)),
      integral_add iR (iA.const_mul (2*C+C*l+m)),integral_const_mul,integral_const_mul,
      integral_div,hN,sub_zero]
  rw [hleft,hright] at hh

  exact absorb_energy C l m beta _ _ _ _ _ hC hl hm hb
    (integral_nonneg_of_ae hU) (integral_nonneg_of_ae hA) (integral_nonneg_of_ae hB) hh

end Asakura.Chapter5
