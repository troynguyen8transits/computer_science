import Downstream.InverseLevels
import ExplicitCost.GroupingPoly
import CountedInstance.Main

set_option autoImplicit false

/-! The clique-size adapter is a single polynomial-time function for every
recursion level. The algorithm and quantitative clique theorem are imported
from Anthropic's CountedInstance.Main; all adaptation lemmas here are downstream.
-/

namespace CSPConsequence.UniformClique

open Groundwork Printed QueryMachines ExplicitCost

abbrev U := List Unit
abbrev Input := U × U × U

def arg (kf : U × U → Option U) (p : CliqueInput) : Input :=
  (InverseLevels.inverse kf p.1,p.2)

theorem arg_polyT (kf : U × U → Option U) (hKF : PolyT kf) : PolyT (arg kf) := by
  have hi := InverseLevels.inverse_polyT kf hKF
  exact PolyT.prodMk (hi.comp (by fun_prop)) (by fun_prop)

theorem arg_of {K : ℕ → ℕ} (kf : U × U → Option U)
    (hC : CliqueLevels.ComputesLevels K kf) (h0 : 2 ≤ K 0)
    (hstep : ∀ l, K l < K (l+1)) (l lam B : ℕ) :
    arg kf (unary (K l),unary lam,unary B) = (unary l,unary lam,unary B) := by
  unfold arg
  rw [InverseLevels.inverse_correct kf hC h0 hstep]

theorem solvesCliques {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}
    (E : QueryMachine TableQuery ℤ Input ℤ) (kf : U × U → Option U)
    (hS : CliqueLevels.Solves E K e C₀)
    (hC : CliqueLevels.ComputesLevels K kf) (h0 : 2 ≤ K 0)
    (hstep : ∀ l, K l < K (l+1)) (l lam B : ℕ) (hlam : 1 ≤ lam) (hB : 1 ≤ B) :
    SolvesCliques E (arg kf (unary (K l),unary lam,unary B)) (K l) lam B
      ⌈CliqueLevels.bound (e l) (K l) C₀ lam B⌉₊
      ⌈CliqueLevels.bound (e l) (K l) C₀ lam B⌉₊ := by
  rw [arg_of kf hC h0 hstep]
  intro W hW
  obtain ⟨T,S,hr,hT,hS⟩ := hS l lam B W hlam hB hW
  have ht : T ≤ ⌈CliqueLevels.bound (e l) (K l) C₀ lam B⌉₊ := by
    exact_mod_cast hT.trans (Nat.le_ceil _)
  have hs : S ≤ ⌈CliqueLevels.bound (e l) (K l) C₀ lam B⌉₊ := by
    exact_mod_cast hS.trans (Nat.le_ceil _)
  exact hr.mono ht hs

theorem grouping_poly (E : QueryMachine TableQuery ℤ Input ℤ)
    (kf : U × U → Option U) (hE : E.PolyTimeSteps) (hKF : PolyT kf) :
    (groupingData E (arg kf)).PolyTimeSteps :=
  groupingPoly.2 Input E (arg kf) hE (arg_polyT kf hKF)

theorem backend_exists : ∃ (E : QueryMachine TableQuery ℤ Input ℤ)
    (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : U × U → Option U),
    E.PolyTimeSteps ∧ CliqueLevels.Solves E K e C₀ ∧ CliqueLevels.Levels K e C₀ ∧
    CliqueLevels.ComputesLevels K kf ∧
    ∃ A : ℝ, ∀ l, e l ≤ A / Real.sqrt (MainTheoremForms.lg (K l)) := by
  obtain ⟨c,x₀,C₀,D,Alg,_,_,_,_,_,hpoly,hsolves,hlevels,hcompute,_,he⟩ :=
    CountedInstance.theRecursionMeetsTheHypothesis
  exact ⟨_,_,_,_,_,hpoly,hsolves,hlevels,hcompute,_,he⟩

#print axioms arg_polyT
#print axioms arg_of
#print axioms solvesCliques
#print axioms grouping_poly
#print axioms backend_exists

end CSPConsequence.UniformClique
