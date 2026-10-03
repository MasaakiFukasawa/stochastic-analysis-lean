import Chapter4NoiseGridAlgebra
import Chapter4EulerGrid

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable def eulerNoiseMap {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (h : ℝ) : (n : ℕ) → (Fin dim → ℝ) → (Fin n → Fin noise → ℝ) → (Fin dim → ℝ)
  | 0,x,_ => x
  | n+1,x,z => fun i =>
      let y := eulerNoiseMap μ σ h n x (fun k => z k.castSucc)
      y i+μ i y*h+∑ j,σ i j y*z (Fin.last n) j

lemma euler_noise_map_continuous {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j)) (h : ℝ) :
    ∀ n,Continuous (fun z : (Fin dim → ℝ) × (Fin n → Fin noise → ℝ) => eulerNoiseMap μ σ h n z.1 z.2) := by
  intro n
  induction n with
  | zero => exact continuous_fst
  | succ n ih =>
    have hy : Continuous (fun z : (Fin dim → ℝ) × (Fin (n+1) → Fin noise → ℝ) =>
        eulerNoiseMap μ σ h n z.1 (fun k => z.2 k.castSucc)) :=
      ih.comp (continuous_fst.prodMk (continuous_pi (fun k => (continuous_apply k.castSucc).comp continuous_snd)))
    apply continuous_pi
    intro i
    exact (((continuous_apply i).comp hy).add (((hμ i).comp hy).mul_const h)).add
      (continuous_finset_sum _ (fun j _ => ((hσ i j).comp hy).mul
        ((continuous_apply j).comp ((continuous_apply (Fin.last n)).comp continuous_snd))))

lemma euler_noise_map_grid {Ω : Type*} {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (W : Fin noise → ℝ → Ω → ℝ) (ξ : Ω → Fin dim → ℝ) (h : ℝ) :
    ∀ n w,eulerNoiseMap μ σ h n (ξ w) (finiteNoiseGrid W h n w)=eulerGrid μ σ W ξ h n w := by
  intro n
  induction n with
  | zero => intro w;rfl
  | succ n ih =>
    intro w
    have hz : (fun k : Fin n => finiteNoiseGrid W h (n+1) w k.castSucc)=finiteNoiseGrid W h n w := rfl
    simp only [eulerNoiseMap,hz,ih,eulerGrid]
    rfl

end Asakura.Chapter4
