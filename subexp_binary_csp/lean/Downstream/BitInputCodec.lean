import Downstream.DynamicPreparation
import ToTuring.Lib.List3
import ToTuring.Lib.Unary

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Explicit binary front end for the complete rectangular CSP table format.
Five unary fields k,D,g,b,K are terminated by false bits. They are followed by
the k-by-k edge table and k-by-k-by-D-by-D relation table, row-major.
Malformed words still have a total decoder. Sparse tuple-list normalization is
a separate obligation; complete tables are not silently expanded here. -/
namespace CSPConsequence.BitInputCodec
open Groundwork FiniteInput ProviderParameters DynamicPreparation NodeRefinement

def frame (u : List Unit) (w : List Bool) : List Bool := u.map (fun _ => true) ++ false :: w
def readUnits (w : List Bool) : List Unit := (w.takeWhile id).map (fun _ => ())
def skip (w : List Bool) : List Bool := (w.dropWhile id).tail

theorem readUnits_frame (u : List Unit) (w : List Bool) : readUnits (frame u w) = u := by
  induction u with
  | nil => simp [readUnits,frame]
  | cons a u ih => cases a; simpa [readUnits,frame] using congrArg (List.cons ()) ih

theorem skip_frame (u : List Unit) (w : List Bool) : skip (frame u w) = w := by
  induction u with
  | nil => simp [skip,frame]
  | cons a u ih => simpa [skip,frame] using ih

def rest : Nat → List Bool → List Bool
  | 0,w => w
  | n+1,w => skip (rest n w)

def header (n : Nat) (w : List Bool) : List Unit := readUnits (rest n w)

@[fun_prop] theorem frame_polyT : PolyT (fun p : List Unit × List Bool => frame p.1 p.2) := by
  unfold frame
  fun_prop
@[fun_prop] theorem readUnits_polyT : PolyT readUnits := by unfold readUnits; fun_prop
@[fun_prop] theorem skip_polyT : PolyT skip := by unfold skip; fun_prop
@[fun_prop] theorem rest_polyT (n : Nat) : PolyT (rest n) := by
  induction n with
  | zero => exact PolyT.id'
  | succ n ih =>
    change PolyT (fun w => skip (rest n w))
    exact PolyT.comp skip_polyT ih
@[fun_prop] theorem header_polyT (n : Nat) : PolyT (header n) := by
  change PolyT (fun w => readUnits (rest n w))
  exact PolyT.comp readUnits_polyT (rest_polyT n)

def row {α : Type} (width i : Nat) (w : List α) : List α := (w.drop (i*width)).take width
def splitRows {α : Type} (n width : Nat) (w : List α) : List (List α) :=
  (List.range n).map (fun i => row width i w)

/-- Generic form of the constant-width block argument in Anthropic's
StepMachines.Prog.Decode.block_flatten, now also for lists of lists. -/
theorem row_flatten {α : Type} {width : Nat} (L : List (List α))
    (h : ∀ l ∈ L, l.length = width) (i : Nat) (hi : i < L.length) :
    row width i L.flatten = L[i] := by
  induction L generalizing i with
  | nil => simp at hi
  | cons a L ih =>
    have ha := h a (by simp)
    cases i with
    | zero => simpa only [row,Nat.zero_mul,List.drop_zero,List.flatten_cons,List.getElem_cons_zero,← ha]
        using (List.take_left (l₁ := a) (l₂ := L.flatten))
    | succ i =>
      have hs : (a ++ L.flatten).drop ((i+1)*width) = L.flatten.drop (i*width) := by
        rw [Nat.succ_mul,Nat.add_comm,← List.drop_drop,← ha,List.drop_left]
      simpa only [row,List.flatten_cons,List.getElem_cons_succ,hs] using
        ih (fun l hl => h l (by simp [hl])) i (by simpa using hi)

theorem splitRows_flatten {α : Type} {width : Nat} (L : List (List α))
    (h : ∀ l ∈ L, l.length = width) : splitRows L.length width L.flatten = L := by
  apply List.ext_getElem
  · simp [splitRows]
  · intro i hi hj
    simpa only [splitRows,List.getElem_map,List.getElem_range] using row_flatten L h i hj

theorem splitRows_polyT {α β : Type} [Enc α] [Enc β]
    (n width : α → Nat) (w : α → List β)
    (hn : Unary n) (hw : PolyT width) (hl : PolyT w) :
    PolyT (fun x => splitRows (n x) (width x) (w x)) := by
  have hr := PolyT.range hn
  unfold splitRows row
  apply PolyT.map
  · fun_prop
  · exact hr

def edgeBits (w : List Bool) : List Bool := (rest 5 w).take ((header 0 w).length^2)
def relationBits (w : List Bool) : List Bool := (rest 5 w).drop ((header 0 w).length^2)

@[fun_prop] theorem edgeBits_polyT : PolyT edgeBits := by unfold edgeBits; fun_prop
@[fun_prop] theorem relationBits_polyT : PolyT relationBits := by unfold relationBits; fun_prop

def edgeRows (w : List Bool) : EdgeTable :=
  splitRows (header 0 w).length (header 0 w).length (edgeBits w)
def leafRows (w : List Bool) : List (List Bool) :=
  splitRows ((header 0 w).length^2*(header 1 w).length) (header 1 w).length (relationBits w)
def pairRows (w : List Bool) : List (List (List Bool)) :=
  splitRows ((header 0 w).length^2) (header 1 w).length (leafRows w)
def relationRows (w : List Bool) : RelationTable :=
  splitRows (header 0 w).length (header 0 w).length (pairRows w)

theorem header_unary (n : Nat) : Unary (fun w => (header n w).length) := Unary.of_length (header_polyT n)

@[fun_prop] theorem edgeRows_polyT : PolyT edgeRows :=
  splitRows_polyT _ _ _ (header_unary 0) (by fun_prop) edgeBits_polyT
@[fun_prop] theorem leafRows_polyT : PolyT leafRows := by
  change PolyT (fun w : List Bool =>
    splitRows ((header 0 w).length^2*(header 1 w).length) (header 1 w).length (relationBits w))
  have hn := ((header_unary 0).mul (header_unary 0)).mul (header_unary 1)
  simpa only [pow_two] using splitRows_polyT
    (fun w => (header 0 w).length*(header 0 w).length*(header 1 w).length)
    (fun w => (header 1 w).length) relationBits hn (by fun_prop) relationBits_polyT
@[fun_prop] theorem pairRows_polyT : PolyT pairRows := by
  change PolyT (fun w : List Bool =>
    splitRows ((header 0 w).length^2) (header 1 w).length (leafRows w))
  simpa only [pow_two] using splitRows_polyT
    (fun w => (header 0 w).length*(header 0 w).length)
    (fun w => (header 1 w).length) leafRows
    ((header_unary 0).mul (header_unary 0)) (by fun_prop) leafRows_polyT
@[fun_prop] theorem relationRows_polyT : PolyT relationRows :=
  splitRows_polyT _ _ _ (header_unary 0) (by fun_prop) pairRows_polyT

def decode (w : List Bool) : PreparedInput :=
  (((header 0 w,(header 1 w,(edgeRows w,relationRows w))),
    (header 2 w,header 3 w)),header 4 w)

theorem decode_polyT : PolyT decode := by unfold decode; fun_prop

def encode (p : PreparedInput) : List Bool :=
  frame p.1.1.1 (frame p.1.1.2.1 (frame p.1.2.1 (frame p.1.2.2 (frame p.2
    (p.1.1.2.2.1.flatten ++ p.1.1.2.2.2.flatten.flatten.flatten)))))

theorem encode_polyT : PolyT encode := by unfold encode; fun_prop

#print axioms decode_polyT
#print axioms encode_polyT
#print axioms splitRows_flatten
end CSPConsequence.BitInputCodec
