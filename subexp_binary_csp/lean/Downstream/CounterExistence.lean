import Downstream.LevelCounter
import GeneralPieces.Num.PartA

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! An unconditional, same-version package of the actual counting machine and
its explicit abstract-step bound. The imported Anthropic algorithm supplies
the backend; this is not yet the native asymptotic CSP theorem. -/

namespace CSPConsequence.CounterExistence

open Groundwork Printed QueryMachines NodeRefinement

structure Counter (Δ : ℕ) where
  K : ℕ → ℕ
  e : ℕ → ℝ
  C₀ : ℕ
  C₁ : ℕ
  A : ℝ
  kf : UniformClique.U × UniformClique.U → Option UniformClique.U
  machine : Stepped DynamicPreparation.PreparedInput ℤ
  poly : Nonempty (IsPolyT machine)
  levels : CliqueLevels.Levels K e C₀
  growth10 : ∀ l, K (l+1) ≤ K l^10
  computes : CliqueLevels.ComputesLevels K kf
  rate : ∀ l, e l ≤ A / Real.sqrt (MainTheoremForms.lg (K l))
  correct : ∀ {k D g : ℕ} (I : Instance k D) (b l : ℕ)
    (hg : 0 < g) (hpos : 0 < D), 1 ≤ b → D ≤ 2^b → 1 ≤ Δ →
    (∀ a, I.degree a ≤ Δ) → 2 ≤ g → g = 3*(K l)^8 →
    LevelCounter.RunBound I b Δ (K l) C₁
      (LevelCounter.budget (e l) C₀ (K l) g (Δ*b*(k/g+1))
        ((k/g+1)+(k/g+1)*(k/g+1)+1)
        (BitNetwork.data I ⟨0,hpos⟩ b (balanced hg)).U)
      hg hpos machine

theorem exists_counter (Δ : ℕ) : Nonempty (Counter Δ) := by
  obtain ⟨c,x₀,C₀,D,Alg,_,_,_,hx,_,hpoly,hsolves,hlevels,hcompute,_,he⟩ :=
    CountedInstance.theRecursionMeetsTheHypothesis
  obtain ⟨C₁,hC⟩ := LevelCounter.contract _ _ _ _ _ hsolves hcompute hlevels
  refine ⟨⟨_,_,C₀,C₁,_,_,_,
    ConcreteSolver.machine_poly Δ _ _ hpoly hcompute.1,
    hlevels,?_,hcompute,he,?_⟩⟩
  · intro l
    exact (GeneralPieces.PartA.K_lt_le x₀ l (by omega)).2
  · intro k D g I b l hg hpos hb hD hΔ hdeg hg2 hgK
    exact hC I b Δ l hg hpos hb hD hΔ hdeg hg2 hgK

#print axioms exists_counter

end CSPConsequence.CounterExistence
