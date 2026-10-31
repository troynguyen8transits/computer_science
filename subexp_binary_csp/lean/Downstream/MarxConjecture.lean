import Downstream.GraphWidthTransport
import Downstream.SparseGraphTransfer
import Downstream.SparseUniformRuntime
import Downstream.SparseOrdinarySize

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

/-! Literal quantifiers of Marx (2010), Conjecture 1.4, printed page 88.
Graphs are finite simple graphs with canonically numbered vertices. The input
size is the ordinary sum of explicit binary field lengths, with list/vertex
counts. The sparse native encoding has proved polynomial overhead in this
measure. Correctness is required on every valid binary CSP, not just the class.
This statement is separate from the paper's ETH-conditional Theorem 1.3. -/
namespace CSPConsequence.MarxConjecture
noncomputable section
open Groundwork Turing SparseRelabelPreparation GraphWidthNumber

abbrev Graph := Σ k : ℕ, SimpleGraph (Fin k)
def width (G : Graph) : ℕ := treewidth G.2
def inputGraph (p : Input) : Graph := ⟨p.1.length,SparseGraphTransfer.primal p⟩
def Unbounded (C : Graph → Prop) : Prop := ∀ w : ℕ, ∃ G, C G ∧ w < width G

def Correct (N : TM2ComputableAux Bool Bool) : Prop :=
  ∀ p : Input, SparseNormalization.ScopeBounded p.1.length p.2.2 →
    ∃ t b, Nonempty (TM2OutputsInTime N.tm
      ((SparseRawBits.encode p).map N.inputAlphabet.invFun)
      (some ([b].map N.outputAlphabet.invFun)) t) ∧
      (b = true ↔ SparseDecision.Satisfiable p)

def Fast (C : Graph → Prop) (N : TM2ComputableAux Bool Bool)
    (f : Graph → ℝ) (h : ℝ → ℝ) : Prop :=
  ∀ p : Input, SparseNormalization.ScopeBounded p.1.length p.2.2 → C (inputGraph p) →
    ∃ t b, Nonempty (TM2OutputsInTime N.tm
      ((SparseRawBits.encode p).map N.inputAlphabet.invFun)
      (some ([b].map N.outputAlphabet.invFun)) t) ∧
      (b = true ↔ SparseDecision.Satisfiable p) ∧
      (t:ℝ) ≤ f (inputGraph p)*(SparseSizeBounds.ordinarySize p:ℝ)^(h (width (inputGraph p)))

def Counterexample : Prop :=
  ∃ (C : Graph → Prop) (N : TM2ComputableAux Bool Bool) (f : Graph → ℝ) (h : ℝ → ℝ),
    Unbounded C ∧ (h =o[Filter.atTop] (fun x => x)) ∧
      (∀ i, Finite (N.tm.Γ i)) ∧ Correct N ∧ Fast C N f h

def Statement : Prop := ¬Counterexample

def tail (cutoff : ℕ) (G : Graph) : Prop :=
  ∃ n, cutoff ≤ GraphFamily.familySize n ∧ Nonempty (G.2 ≃g GraphFamily.graph n)

theorem tail_unbounded (cutoff : ℕ) : Unbounded (tail cutoff) := by
  intro w
  obtain ⟨n,hcut,hw⟩ := GraphWidthNumber.tail_unbounded cutoff w
  exact ⟨⟨GraphFamily.familySize n,GraphFamily.graph n⟩,
    ⟨n,hcut,⟨SimpleGraph.Iso.refl⟩⟩,hw⟩

/-- The actual imported counting backend, global sparse native machine and
source-checked spectral family supply the witnesses. No fast solver is a
hypothesis of this theorem. -/
theorem counterexample : Counterexample := by
  let Δ := Fintype.card OAI.IndependentSetsGames.Foundations.PCP.ExpanderFamily.Port
  have hΔ : 1 ≤ Δ := Fintype.card_pos
  obtain ⟨c,N,q,hfinite,hcorrect,hhost⟩ := SparseNativeMachine.exists_native Δ hΔ
  let cutoff := max 64 (c.K 0^32)
  let C := NativeFastRuntime.exponentialCoefficient c q
  let A := 2*C/Real.log 2
  let P : ℝ := SparseUniformRuntime.degree c q
  let H := 2*(P+32*A)
  let f : Graph → ℝ := fun G => SparseUniformRuntime.prefactor c q G.1*
    36^(P+SparseUniformRuntime.rate c q G.1)
  refine ⟨tail cutoff,N,f,(fun w : ℝ => H*w/Real.sqrt (Real.log w)),
    tail_unbounded cutoff,SublinearRate.sublinear H,hfinite,hcorrect,?_⟩
  intro p hs hp
  obtain ⟨n,hcut,⟨e⟩⟩ := hp
  have hcard := SparseGraphTransfer.iso_card p n e
  have h64 : 64 ≤ GraphFamily.familySize n := (le_max_left _ _).trans hcut
  have hlarge : c.K 0^32 ≤ p.1.length := by
    rw [hcard]
    exact (le_max_right _ _).trans hcut
  have hi := SparseGraphTransfer.iso_nonisolated p n e
  have hd := SparseGraphTransfer.iso_degree p n e
  have htweq := GraphWidthTransport.treewidth_iso e
  change treewidth (SparseGraphTransfer.primal p) = treewidth (GraphFamily.graph n) at htweq
  have hcomp := GraphWidthTransport.family_comparison n h64
  have hw : 2 ≤ treewidth (SparseGraphTransfer.primal p) := by rw [htweq]; exact hcomp.1
  have hwk : treewidth (SparseGraphTransfer.primal p) ≤ p.1.length := by
    rw [htweq,hcard]
    exact family_tw_le n
  have hkw : (p.1.length:ℝ) ≤ 32*(treewidth (SparseGraphTransfer.primal p):ℝ) := by
    rw [htweq,hcard]
    exact hcomp.2
  have hk : 2 ≤ p.1.length := hw.trans hwk
  obtain ⟨t,hnative,ht⟩ := SparseUniformRuntime.fast_for_host c hΔ N q hhost p hlarge hd hi
  have hne := SparseDecisionRuns.nonempty_nonisolated p (by omega) hi
  have hc := SparseDecisionRuns.check_nonisolated p hi
  have hsat : SparseDecision.positive ((semantic p).count:ℤ) = true ↔ SparseDecision.Satisfiable p := by
    rw [SparseDecision.count_positive]
    exact ((SparseIsolates.original_decision_iff p hs hne).trans (and_iff_right hc)).symm
  refine ⟨t,_,hnative,hsat,?_⟩
  have hC : 0 ≤ C := SparseUniformRuntime.exponential_nonneg c hΔ q
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR : 0 ≤ SparseUniformRuntime.rate c q p.1.length :=
    SparsePowerAbsorption.rate_nonneg hC (by exact_mod_cast hk)
  have hP : 0 ≤ P := Nat.cast_nonneg _
  have htrans := GraphWidthTransport.exponent_transfer hA hP
    (by exact_mod_cast hw) (by exact_mod_cast hwk) hkw
  have hRbound : 2*(P+SparseUniformRuntime.rate c q p.1.length) ≤
      H*(treewidth (SparseGraphTransfer.primal p):ℝ)/
        Real.sqrt (Real.log (treewidth (SparseGraphTransfer.primal p):ℝ)) := by
    change P+A*(p.1.length:ℝ)/Real.sqrt (Real.log (p.1.length:ℝ)) ≤ _ at htrans
    change 2*(P+A*(p.1.length:ℝ)/Real.sqrt (Real.log (p.1.length:ℝ))) ≤ _
    calc
      _ ≤ 2*((P+32*A)*(treewidth (SparseGraphTransfer.primal p):ℝ)/
          Real.sqrt (Real.log (treewidth (SparseGraphTransfer.primal p):ℝ))) :=
        mul_le_mul_of_nonneg_left htrans (by norm_num)
      _ = _ := by dsimp [H]; ring
  have hPref : 0 ≤ SparseUniformRuntime.prefactor c q p.1.length := by
    unfold SparseUniformRuntime.prefactor
    exact mul_nonneg (SparseUniformRuntime.factor_nonneg c q) (Real.rpow_nonneg (by norm_num) _)
  have hpower := SparseOrdinarySize.power_transfer p hPref (add_nonneg hP hR) hRbound
  exact ht.trans hpower

theorem not_statement : ¬Statement := fun h => h counterexample

#print axioms tail_unbounded
#print axioms counterexample
#print axioms not_statement
end
end CSPConsequence.MarxConjecture
