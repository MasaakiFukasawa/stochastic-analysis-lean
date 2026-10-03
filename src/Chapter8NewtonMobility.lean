import Chapter8NewtonHamiltonian

open scoped BigOperators
namespace Asakura.Chapter8
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

def newtonMobility (d : ℕ) (m γ : ℝ) : Fin (d+d) → Fin (d+d) → ℝ :=
  Fin.addCases
    (fun i => Fin.addCases (fun _ => 0) (fun j => if i=j then -m⁻¹ else 0))
    (fun i => Fin.addCases (fun j => if i=j then m⁻¹ else 0) (fun j => if i=j then γ/m^2 else 0))

def newtonNoise (d : ℕ) (a : ℝ) : Fin (d+d) → Fin d → ℝ :=
  Fin.addCases (fun _ _ => 0) (fun i j => if i=j then a else 0)

theorem newton_einstein_blocks (d : ℕ) (m γ β a : ℝ)
    (ha : a^2=2*β⁻¹*γ/m^2) :
    ∀ i j,∑ k,newtonNoise d a i k*newtonNoise d a j k=
      β⁻¹*(newtonMobility d m γ i j+newtonMobility d m γ j i) := by
  intro i j
  refine Fin.addCases ?_ ?_ i <;> intro i
  · refine Fin.addCases ?_ ?_ j <;> intro j
    · simp only [newtonNoise,newtonMobility,Fin.addCases_left,Fin.addCases_right]; simp
    · simp only [newtonNoise,newtonMobility,Fin.addCases_left,Fin.addCases_right]
      by_cases hij : i=j <;> simp [hij,eq_comm]
  · refine Fin.addCases ?_ ?_ j <;> intro j
    · simp only [newtonNoise,newtonMobility,Fin.addCases_left,Fin.addCases_right]
      by_cases hij : i=j <;> simp [hij,eq_comm]
    · simp only [newtonNoise,newtonMobility,Fin.addCases_left,Fin.addCases_right]
      by_cases hij : i=j
      · subst j
        simp [← pow_two,ha]
        ring
      · simp [hij,eq_comm]

theorem newton_drift_blocks {d : ℕ}
    (U : (Fin d → ℝ) → ℝ) (hU : Differentiable ℝ U)
    (m γ : ℝ) (hm : m≠0) (z : Fin (d+d) → ℝ) (i : Fin d) :
    -(∑ j,newtonMobility d m γ (Fin.castAdd d i) j*
      fderiv ℝ (newtonHamiltonian U m) z (Pi.single j 1))=velocityProjection d z i ∧
    -(∑ j,newtonMobility d m γ (Fin.natAdd d i) j*
      fderiv ℝ (newtonHamiltonian U m) z (Pi.single j 1))=
      -(fderiv ℝ U (positionProjection d z) (Pi.single i 1)+γ*velocityProjection d z i)/m := by
  have hg := newton_hamiltonian_gradient U hU m z i
  constructor
  · rw [Fin.sum_univ_add]
    simp only [newtonMobility,Fin.addCases_left,Fin.addCases_right]
    simp only [ite_mul,zero_mul,Finset.sum_const_zero,zero_add,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rw [hg.2]
    field_simp
    <;> ring
  · rw [Fin.sum_univ_add]
    simp only [newtonMobility,Fin.addCases_left,Fin.addCases_right]
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    rw [hg.1,hg.2]
    field_simp
    <;> ring

end
end Asakura.Chapter8
