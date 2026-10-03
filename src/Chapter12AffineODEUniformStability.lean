import Chapter12AffineODEUniformBounds
import Chapter12AffineForcingDifference
import Chapter12UniformVolterraDerivativeStability

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem affine_ode_uniform_stability {E α : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T : ℝ) (hT : 0≤T)
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (hSeq : ∀q t,S q t=q t+∫s in 0..t.val,b (S q (projIcc 0 T hT s)))
    (N : α → ℕ) (a a' : α → C(Icc (0:ℝ) T,E))
    (L M : ∀i,(Fin (N i) → ℝ) →L[ℝ] C(Icc (0:ℝ) T,E))
    (B D : ℝ) (hB : 0≤B) (hD : 0≤D) (δ : α → ℝ) (hδ : ∀i,0≤δ i)
    (hLB : ∀i t,Real.sqrt (∑j,‖L i (Pi.single j 1) t‖^2)≤B)
    (hMB : ∀i t,Real.sqrt (∑j,‖M i (Pi.single j 1) t‖^2)≤B)
    (hLD : ∀i t,Real.sqrt (∑j,‖L i (Pi.single j 1) t-M i (Pi.single j 1) t‖^2)≤D*δ i) :
    ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀i z t,
      Real.sqrt (∑j : Fin k → Fin (N i),
        ‖(iteratedFDeriv ℝ k (fun y => S (a i+L i y)) z (fun r => Pi.single (j r) 1)) t-
          (iteratedFDeriv ℝ k (fun y => S (a' i+M i y)) z (fun r => Pi.single (j r) 1)) t‖^2)≤
        C*(‖S (a i+L i z)-S (a' i+M i z)‖+δ i) := by
  classical
  let Q := fun i (z : Fin (N i) → ℝ) => a i+L i z
  let Q' := fun i (z : Fin (N i) → ℝ) => a' i+M i z
  let X := fun i => S ∘ Q i
  let Y := fun i => S ∘ Q' i
  have hQ i : ContDiff ℝ ∞ (Q i) := contDiff_const.add (L i).contDiff
  have hQ' i : ContDiff ℝ ∞ (Q' i) := contDiff_const.add (M i).contDiff
  have hX i : ContDiff ℝ ∞ (X i) := hS.comp (hQ i)
  have hY i : ContDiff ℝ ∞ (Y i) := hS.comp (hQ' i)
  have heX i z t : X i z t=Q i z t+∫s in 0..t.val,b (X i z (projIcc 0 T hT s)) := hSeq (Q i z) t
  have heY i z t : Y i z t=Q' i z t+∫s in 0..t.val,b (Y i z (projIcc 0 T hT s)) := hSeq (Q' i z) t
  have hxB := affine_ode_uniform_bounds b hb hbound T hT S hS hSeq N a L B hB hLB
  have hyB := affine_ode_uniform_bounds b hb hbound T hT S hS hSeq N a' M B hB hMB
  have hexC : ∀k:ℕ,∃C:ℝ,0≤C ∧ (1≤k → ∀i z t,
      Real.sqrt (∑j : Fin k → Fin (N i),‖(iteratedFDeriv ℝ k (X i) z (fun r => Pi.single (j r) 1)) t‖^2)≤C ∧
      Real.sqrt (∑j : Fin k → Fin (N i),‖(iteratedFDeriv ℝ k (Y i) z (fun r => Pi.single (j r) 1)) t‖^2)≤C) := by
    intro k
    by_cases hk : 1≤k
    · obtain ⟨C,hC,hc⟩ := hxB k hk
      obtain ⟨C',hC',hc'⟩ := hyB k hk
      refine ⟨C+C',add_nonneg hC hC',?_⟩
      intro _ i z t
      exact ⟨(hc i z t).trans (le_add_of_nonneg_right hC'),(hc' i z t).trans (le_add_of_nonneg_left hC)⟩
    · exact ⟨0,le_rfl,fun h => (hk h).elim⟩
  choose C hC hc using hexC
  let ε := fun i z => ‖X i z-Y i z‖+δ i
  have hε i z : 0≤ε i z := add_nonneg (norm_nonneg _) (hδ i)
  have hXY i z t : ‖X i z t-Y i z t‖≤ε i z :=
    ((X i z-Y i z).norm_coe_le_norm t).trans (le_add_of_nonneg_right (hδ i))
  have hQD k (hk : 1≤k) i z t :
      Real.sqrt (∑j : Fin k → Fin (N i),
        ‖(iteratedFDeriv ℝ k (Q i) z (fun r => Pi.single (j r) 1)) t-
          (iteratedFDeriv ℝ k (Q' i) z (fun r => Pi.single (j r) 1)) t‖^2)≤(if k=1 then D else 0)*ε i z := by
    apply affine_forcing_array_difference (L i) (M i) (a i) (a' i) D (ε i z) hD (hε i z) _ k hk z t
    intro s
    exact (hLD i s).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) hD)
  exact uniform_volterra_derivative_stability (fun i => Fin (N i) → ℝ) (fun i => Fin (N i)) b hb hbound T hT Q Q' X Y
    hQ hQ' hX hY heX heY (fun _ j => Pi.single j 1) (fun k => if k=1 then D else 0) C
    (fun k => by split_ifs <;> positivity) hC ε hε hXY hQD
    (fun k hk i z t => (hc k hk i z t).1) (fun k hk i z t => (hc k hk i z t).2)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.affine_ode_uniform_stability
