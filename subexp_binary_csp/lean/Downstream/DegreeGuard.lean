import Downstream.TableRefinement
import ToTuring.Lib.Nat1b

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! A computable degree guard, so the fast counter need not be trusted on
inputs outside its verified degree promise. -/

namespace CSPConsequence.DegreeGuard

open Groundwork FiniteInput Finset

def neighbors (p : Input × ℕ) : List ℕ :=
  (List.range (vertices p.1)).filter (fun v => decide (v ≠ p.2) && edgeAt p.1 p.2 v)

@[fun_prop] theorem neighbors_polyT : PolyT neighbors := by
  have hr : PolyT (fun p : Input × ℕ => List.range (vertices p.1)) :=
    PolyT.range (Unary.of_length (by fun_prop))
  have he : PolyT (fun p : (Input × ℕ) × ℕ => edgeAt p.1.1 p.1.2 p.2) :=
    PolyT.comp (g := fun p : (Input × ℕ) × ℕ => (p.1.1,(p.1.2,p.2)))
      FiniteInput.edgeAt_polyT (by fun_prop)
  have hp : PolyT (fun p : (Input × ℕ) × ℕ => decide (p.2 ≠ p.1.2) && edgeAt p.1.1 p.1.2 p.2) := by
    exact PolyT.and' (by fun_prop) he
  unfold neighbors
  exact PolyT.filter hp hr

theorem finRange_values (k : ℕ) : (List.finRange k).map Fin.val = List.range k := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [List.finRange]

theorem neighbors_length {k D : ℕ} (I : Instance k D) (a : Fin k) :
    (neighbors (tabulate I,a.val)).length = I.degree a := by
  classical
  let f : Fin k → Bool := fun v => decide (v ≠ a) && I.edge a v
  have he : neighbors (tabulate I,a.val) = ((List.finRange k).filter f).map Fin.val := by
    unfold neighbors
    rw [vertices_tabulate,← finRange_values,List.filter_map]
    congr 1
    apply List.filter_congr
    intro v _
    simp [f,edgeAt_tabulate,Fin.ext_iff]
  rw [he,List.length_map,← List.toFinset_card_of_nodup ((List.nodup_finRange k).filter f)]
  have hs : ((List.finRange k).filter f).toFinset =
      (univ.erase a).filter (fun v => I.edge a v = true) := by
    ext v
    simp [f]
  rw [hs]
  rfl

def check (Δ : ℕ) (input : Input) : Bool :=
  (List.range (vertices input)).all (fun a => decide ((neighbors (input,a)).length ≤ Δ))

@[fun_prop] theorem check_polyT (Δ : ℕ) : PolyT (check Δ) := by
  have hr : PolyT (fun input : Input => List.range (vertices input)) :=
    PolyT.range (Unary.of_length (by fun_prop))
  unfold check
  exact PolyT.all (PolyT.decide_le (PolyT.length neighbors_polyT) (PolyT.const Δ)) hr

theorem check_of {k D : ℕ} (I : Instance k D) (Δ : ℕ) :
    check Δ (tabulate I) = true ↔ ∀ a, I.degree a ≤ Δ := by
  unfold check
  rw [vertices_tabulate,TableRefinement.all_range_fin]
  simp only [neighbors_length,decide_eq_true_eq]

#print axioms neighbors_polyT
#print axioms neighbors_length
#print axioms check_polyT
#print axioms check_of

end CSPConsequence.DegreeGuard
