import Downstream.SparseIsolates
import Downstream.TotalCounter

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! A globally correct decision program on sparse tuple lists. The original
binary domain cardinality is never expanded. Isolated unary constraints are
checked separately, and the verified total counter handles the reduced domain. -/
namespace CSPConsequence.SparseDecision
open Groundwork SparseNormalization SparseRelabelPreparation
open Groundwork.Stepped

def Satisfiable (p : Input) : Prop :=
  ∃ z : Fin p.1.length → Fin p.2.1, RawValid p.2.2 z

def emptyAnswer (p : Input) : Bool := decide (p.1.length = 0 ∨ 0 < p.2.1)
def positive (z : ℤ) : Bool := decide (0 < z)
def reduced {Δ : ℕ} (c : CounterExistence.Counter Δ) : Stepped Input Bool :=
  mapOut (mapIn prepare (TotalCounter.machine c)) positive

def checked {Δ : ℕ} (c : CounterExistence.Counter Δ) : Stepped Input Bool :=
  ite SparseIsolates.check (reduced c) (ofFun (fun _ => false))
def machine {Δ : ℕ} (c : CounterExistence.Counter Δ) : Stepped Input Bool :=
  ite (fun p => p.2.2.isEmpty) (ofFun emptyAnswer) (checked c)

@[fun_prop] theorem emptyAnswer_polyT : PolyT emptyAnswer := by unfold emptyAnswer; fun_prop
@[fun_prop] theorem positive_polyT : PolyT positive := by unfold positive; fun_prop

theorem machine_poly {Δ : ℕ} (c : CounterExistence.Counter Δ) :
    Nonempty (IsPolyT (machine c)) := by
  obtain ⟨hm⟩ := TotalCounter.machine_poly c
  letI : IsPolyT (TotalCounter.machine c) := hm
  letI : IsPolyT (mapIn prepare (TotalCounter.machine c)) := IsPolyT.mapIn prepare_polyT
  letI : IsPolyT (reduced c) := IsPolyT.mapOut positive_polyT
  letI : IsPolyT (ofFun (fun _ : Input => false)) := IsPolyT.ofFun (by fun_prop)
  letI : IsPolyT (checked c) := IsPolyT.ite SparseIsolates.check_polyT
  letI : IsPolyT (ofFun emptyAnswer) := IsPolyT.ofFun emptyAnswer_polyT
  exact ⟨IsPolyT.ite (by fun_prop)⟩

theorem empty_iff (p : Input) (h : p.2.2 = []) :
    emptyAnswer p = true ↔ Satisfiable p := by
  classical
  simp only [emptyAnswer,decide_eq_true_eq]
  constructor
  · rintro (hk | hD)
    · let z : Fin p.1.length → Fin p.2.1 := fun a => False.elim (by have ha := a.isLt; omega)
      exact ⟨z,by simp [RawValid,h]⟩
    · exact ⟨fun _ => ⟨0,hD⟩,by simp [RawValid,h]⟩
  · rintro ⟨z,hz⟩
    by_cases hk : p.1.length = 0
    · exact Or.inl hk
    · exact Or.inr (Nat.zero_lt_of_lt (z ⟨0,by omega⟩).isLt)

theorem count_positive {k D : ℕ} (I : Instance k D) :
    positive (I.count:ℤ) = true ↔ ∃ z, I.valid z := by
  classical
  simp only [positive,decide_eq_true_eq,Int.natCast_pos,Instance.count,
    Finset.card_pos,Finset.nonempty_def,Finset.mem_filter,Finset.mem_univ,true_and]

theorem reduced_runs {Δ : ℕ} (c : CounterExistence.Counter Δ) (hΔ : 1 ≤ Δ) (p : Input) :
    ∃ T S, (reduced c).Runs p T S (positive ((semantic p).count:ℤ)) := by
  obtain ⟨T,S,hr⟩ := TotalCounter.correct c hΔ (semantic p)
  rw [← prepare_eq_tabulate p] at hr
  exact ⟨_,_,mapOut_runs (mapIn_runs hr)⟩

theorem correct {Δ : ℕ} (c : CounterExistence.Counter Δ) (hΔ : 1 ≤ Δ)
    (p : Input) (hs : ScopeBounded p.1.length p.2.2) :
    ∃ T S b, (machine c).Runs p T S b ∧ (b = true ↔ Satisfiable p) := by
  by_cases he : p.2.2 = []
  · refine ⟨_,_,_,ite_runs_true (by simp [he]) (ofFun_runs emptyAnswer p),empty_iff p he⟩
  · by_cases hc : SparseIsolates.check p = true
    · obtain ⟨T,S,hr⟩ := reduced_runs c hΔ p
      refine ⟨_,_,_,ite_runs_false (by simp [List.isEmpty_eq_false_iff,he])
        (ite_runs_true hc hr),?_⟩
      rw [count_positive]
      exact ((SparseIsolates.original_decision_iff p hs he).trans
        (and_iff_right hc)).symm
    · refine ⟨_,_,false,ite_runs_false (by simp [List.isEmpty_eq_false_iff,he])
        (ite_runs_false (Bool.eq_false_iff.mpr hc) (ofFun_runs (fun _ : Input => false) p)),?_⟩
      simp only [Bool.false_eq_true,false_iff]
      intro hz
      exact hc ((SparseIsolates.original_decision_iff p hs he).mp hz).1

#print axioms machine_poly
#print axioms empty_iff
#print axioms count_positive
#print axioms correct
end CSPConsequence.SparseDecision
