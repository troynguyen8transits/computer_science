import Downstream.ConcreteSolver

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Instantiate the concrete solver's clique obligation with the quantitative
uniform clique theorem. Bounds here count abstract steps; no native asymptotic
or polynomial-space conclusion is asserted. -/

namespace CSPConsequence.LevelCounter

open Groundwork Printed QueryMachines ExplicitCost NodeRefinement QuerySizes

theorem parameters_pos {g : ℕ} (K : ℕ) (N : Eight.SecNetworks.Net g) (P B : ℕ)
    (hK : 2 ≤ K) (hg : 2 ≤ g) (hN : N.Is P B) :
    1 ≤ AppRunningTime.Lof K g ((1:ℝ)/(2*K)) P N.U ∧
    1 ≤ AppRunningTime.B'of K g P B := by
  constructor
  · apply Nat.ceil_pos.mpr
    have hp : (0:ℝ) < P := by exact_mod_cast hN.P_pos
    have hgg : (0:ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    have hkk : (0:ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    positivity
  · unfold AppRunningTime.B'of
    have hprod : 1 ≤ g^2*B := Nat.mul_pos (by positivity) hN.B_pos
    exact hprod.trans (Nat.le_add_left _ _)

noncomputable def budget (e : ℝ) (C₀ K g P B U : ℕ) : ℕ :=
  ⌈CliqueLevels.bound e K C₀ (AppRunningTime.Lof K g ((1:ℝ)/(2*K)) P U)
    (AppRunningTime.B'of K g P B)⌉₊

def RunBound {k D g : ℕ} (I : Instance k D) (b Δ K C₁ 𝒯 : ℕ)
    (hg : 0 < g) (hpos : 0 < D)
    (M : Stepped DynamicPreparation.PreparedInput ℤ) : Prop :=
  let P := Δ*b*(k/g+1)
  let B := (k/g+1)+(k/g+1)*(k/g+1)+1
  ∃ T : ℕ, M.Runs (paramsOf I g b,unary K) (3*T)
    (size (paramsOf I g b)+(𝒯+(g*(P+B)+size (1,2*K))^C₁)+
      room (paramsOf I g b) g P B+4) (I.count:ℤ) ∧
    (T:ℝ) ≤ ((K:ℝ)^g+𝒯*(2:ℝ)^(2*(g:ℝ)*P/K))*((g:ℝ)*(P+B))^C₁

theorem contract (E : QueryMachine TableQuery ℤ UniformClique.Input ℤ)
    (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ)
    (kf : UniformClique.U × UniformClique.U → Option UniformClique.U)
    (hS : CliqueLevels.Solves E K e C₀) (hC : CliqueLevels.ComputesLevels K kf)
    (hL : CliqueLevels.Levels K e C₀) :
    ∃ C₁ : ℕ, ∀ {k D g : ℕ} (I : Instance k D) (b Δ l : ℕ)
      (hg : 0 < g) (hpos : 0 < D), 1 ≤ b → D ≤ 2^b → 1 ≤ Δ →
      (∀ a, I.degree a ≤ Δ) → 2 ≤ g → g = 3*(K l)^8 →
      RunBound I b Δ (K l) C₁
        (budget (e l) C₀ (K l) g (Δ*b*(k/g+1))
          ((k/g+1)+(k/g+1)*(k/g+1)+1)
          (BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)).U)
        hg hpos (ConcreteSolver.machine Δ E kf) := by
  obtain ⟨C₁,hCost⟩ := ConcreteSolver.explicit_cost
  refine ⟨C₁,?_⟩
  intro k D g I b Δ l hg hpos hb hD hΔ hdeg hg2 hgK
  have hn := BitNetwork.is_valid I ⟨0,hpos⟩ hg hb hD hΔ hdeg
  obtain ⟨hlam,hB⟩ := parameters_pos (K l) _ _ _ (hL.K_two l) hg2 hn
  exact hCost I b Δ (K l) hg hpos hb hD hΔ hdeg E kf _ _
    (hL.K_two l) hg2 hgK
    (UniformClique.solvesCliques E kf hS hC (hL.K_two 0) hL.K_lt l _ _ hlam hB)

#print axioms parameters_pos
#print axioms contract

end CSPConsequence.LevelCounter
