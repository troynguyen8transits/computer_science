import Downstream.TableFormulas
import ToTuring.Lib.List2

set_option autoImplicit false

/-! Finite input data for the concrete provider. The context contains only lists
and bits, using the existing injective list/product encodings. Function-valued
Instances are semantic views, not unencoded runtime oracles.
-/

namespace CSPConsequence.FiniteInput

open Groundwork

abbrev EdgeTable := List (List Bool)
abbrev RelationTable := List (List (List (List Bool)))
abbrev Input := List Unit × (List Unit × (EdgeTable × RelationTable))

def vertices (input : Input) : ℕ := input.1.length
def domain (input : Input) : ℕ := input.2.1.length

def edgeAt (input : Input) (a v : ℕ) : Bool :=
  (input.2.2.1.getD a []).getD v false

def relationAt (input : Input) (a v x y : ℕ) : Bool :=
  (((input.2.2.2.getD a []).getD v []).getD x []).getD y false

def instanceOf (input : Input) : Instance (vertices input) (domain input) where
  edge a v := edgeAt input (min a.val v.val) (max a.val v.val)
  symmetric a v := by simp [min_comm, max_comm]
  relation a v x y := relationAt input a.val v.val x.val y.val

def tabulate {k D : ℕ} (I : Instance k D) : Input :=
  (List.replicate k (), List.replicate D (),
    List.ofFn (fun a : Fin k => List.ofFn (fun v : Fin k => I.edge a v)),
    List.ofFn (fun a : Fin k => List.ofFn (fun v : Fin k =>
      List.ofFn (fun x : Fin D => List.ofFn (fun y : Fin D => I.relation a v x y)))))

theorem vertices_tabulate {k D : ℕ} (I : Instance k D) : vertices (tabulate I) = k := by
  simp [vertices, tabulate]

theorem domain_tabulate {k D : ℕ} (I : Instance k D) : domain (tabulate I) = D := by
  simp [domain, tabulate]

theorem edgeAt_tabulate {k D : ℕ} (I : Instance k D) (a v : Fin k) :
    edgeAt (tabulate I) a.val v.val = I.edge a v := by
  simp [edgeAt, tabulate, List.getD_eq_getElem?_getD, List.getElem?_ofFn, a.isLt, v.isLt]

theorem relationAt_tabulate {k D : ℕ} (I : Instance k D)
    (a v : Fin k) (x y : Fin D) :
    relationAt (tabulate I) a.val v.val x.val y.val = I.relation a v x y := by
  simp [relationAt, tabulate, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    a.isLt, v.isLt, x.isLt, y.isLt]

theorem edgeAt_polyT : PolyT (fun p : Input × (ℕ × ℕ) => edgeAt p.1 p.2.1 p.2.2) := by
  unfold edgeAt
  fun_prop

theorem relationAt_polyT : PolyT (fun p : Input × (ℕ × ℕ × ℕ × ℕ) =>
    relationAt p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold relationAt
  fun_prop

#print axioms edgeAt_tabulate
#print axioms relationAt_tabulate
#print axioms edgeAt_polyT
#print axioms relationAt_polyT

end CSPConsequence.FiniteInput
