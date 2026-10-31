import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-! Choose a collection of bounded-mass components whose total lies in a
prescribed interval. This is a finite graph-separator helper. -/
namespace TensorResearch.FiniteMassSelection
open scoped BigOperators

theorem interval {I : Type*} (s : Finset I) (mass : I → Real) (a b : Real)
    (ha : 0 < a) (hsum : a ≤ ∑ i ∈ s, mass i) (hbound : ∀ i ∈ s, mass i ≤ b) :
    ∃ t ⊆ s, a ≤ ∑ i ∈ t, mass i ∧ (∑ i ∈ t, mass i) ≤ a+b := by
  classical
  revert hsum hbound
  induction s using Finset.induction_on with
  | empty =>
    intro hsum _
    simp only [Finset.sum_empty] at hsum
    linarith
  | @insert x s hx ih =>
    intro hsum hbound
    by_cases hr : a ≤ ∑ i ∈ s, mass i
    · obtain ⟨t,ht,hl,hu⟩ := ih hr (fun i hi => hbound i (Finset.mem_insert_of_mem hi))
      exact ⟨t,ht.trans (Finset.subset_insert x s),hl,hu⟩
    · refine ⟨insert x s,Finset.Subset.refl _,hsum,?_⟩
      rw [Finset.sum_insert hx]
      have hb := hbound x (Finset.mem_insert_self x s)
      linarith

#print axioms interval
end TensorResearch.FiniteMassSelection
