import Downstream.SparseNormalization

set_option autoImplicit false

/-! Concrete polynomial-time table preparation from sparse tuple lists when
vertex and domain cardinalities are supplied as unary lists. This representation
charges domain expansion explicitly. For compactly specified domains a support
pruning front end is still needed; no polynomial-in-log-D claim is made here. -/
namespace CSPConsequence.SparsePreparation
open Groundwork SparseNormalization

abbrev Input := List Unit × (List Unit × SparseInput)
def vertices (p : Input) : ℕ := p.1.length
def domain (p : Input) : ℕ := p.2.1.length
def constraints (p : Input) : SparseInput := p.2.2
def vertexList (p : Input) : List ℕ := List.range (vertices p)
def domainList (p : Input) : List ℕ := List.range (domain p)

@[fun_prop] theorem vertexList_polyT : PolyT vertexList :=
  PolyT.range (Unary.of_length (by fun_prop))
@[fun_prop] theorem domainList_polyT : PolyT domainList :=
  PolyT.range (Unary.of_length (by fun_prop))

def prepare (p : Input) : FiniteInput.Input :=
  (p.1,p.2.1,
    (vertexList p).map (fun a => (vertexList p).map (fun b => edgeAt (constraints p) a b)),
    (vertexList p).map (fun a => (vertexList p).map (fun b =>
      (domainList p).map (fun x => (domainList p).map (fun y => relationAt (constraints p) a b x y)))))

@[fun_prop] theorem prepare_polyT : PolyT prepare := by
  unfold prepare constraints
  fun_prop

theorem vertices_prepare (p : Input) : FiniteInput.vertices (prepare p) = vertices p := rfl
theorem domain_prepare (p : Input) : FiniteInput.domain (prepare p) = domain p := rfl

theorem edgeAt_prepare (p : Input) (a b : Fin (vertices p)) :
    FiniteInput.edgeAt (prepare p) a.val b.val = edgeAt (constraints p) a.val b.val := by
  simp [FiniteInput.edgeAt,prepare,vertexList,List.getD_eq_getElem?_getD,
    List.getElem?_range,a.isLt,b.isLt]

theorem relationAt_prepare (p : Input) (a b : Fin (vertices p)) (x y : Fin (domain p)) :
    FiniteInput.relationAt (prepare p) a.val b.val x.val y.val =
      relationAt (constraints p) a.val b.val x.val y.val := by
  simp [FiniteInput.relationAt,prepare,vertexList,domainList,List.getD_eq_getElem?_getD,
    List.getElem?_range,a.isLt,b.isLt,x.isLt,y.isLt]

theorem edge_prepare (p : Input) (a b : Fin (vertices p)) :
    (FiniteInput.instanceOf (prepare p)).edge a b =
      (normalized (vertices p) (domain p) (constraints p)).edge a b := by
  change FiniteInput.edgeAt (prepare p) (min a.val b.val) (max a.val b.val) = _
  rcases le_total a.val b.val with h | h
  · rw [min_eq_left h,max_eq_right h,edgeAt_prepare]
    rfl
  · rw [min_eq_right h,max_eq_left h,edgeAt_prepare,edgeAt_symmetric]
    rfl

theorem relation_prepare (p : Input) (a b : Fin (vertices p)) (x y : Fin (domain p)) :
    (FiniteInput.instanceOf (prepare p)).relation a b x y =
      (normalized (vertices p) (domain p) (constraints p)).relation a b x y :=
  relationAt_prepare p a b x y

theorem valid_prepare_iff (p : Input) (z : Fin (vertices p) → Fin (domain p)) :
    (FiniteInput.instanceOf (prepare p)).valid z ↔
      (normalized (vertices p) (domain p) (constraints p)).valid z := by
  change (∀ a b : Fin (vertices p), a < b →
    (FiniteInput.instanceOf (prepare p)).edge a b = true →
    (FiniteInput.instanceOf (prepare p)).relation a b (z a) (z b) = true) ↔
    (∀ a b : Fin (vertices p), a < b →
    (normalized (vertices p) (domain p) (constraints p)).edge a b = true →
    (normalized (vertices p) (domain p) (constraints p)).relation a b (z a) (z b) = true)
  constructor
  · intro h a b hab he
    have he' := (edge_prepare p a b).trans he
    have hr := h a b hab he'
    exact (relation_prepare p a b (z a) (z b)).symm.trans hr
  · intro h a b hab he
    have he' := (edge_prepare p a b).symm.trans he
    have hr := h a b hab he'
    exact (relation_prepare p a b (z a) (z b)).trans hr

private theorem instance_eq {k D : ℕ} (J J' : Instance k D)
    (he : J.edge = J'.edge) (hr : J.relation = J'.relation) : J = J' := by
  cases J
  cases J'
  cases he
  cases hr
  rfl

theorem count_prepare (p : Input) (hscope : ScopeBounded (vertices p) (constraints p))
    (hni : Nonisolated (vertices p) (constraints p)) :
    (FiniteInput.instanceOf (prepare p)).count = rawCount (k:=vertices p) (D:=domain p) (constraints p) := by
  classical
  let J : Instance (vertices p) (domain p) := FiniteInput.instanceOf (prepare p)
  have he : J.edge = (normalized (vertices p) (domain p) (constraints p)).edge :=
    funext (fun a => funext (fun b => edge_prepare p a b))
  have hr : J.relation = (normalized (vertices p) (domain p) (constraints p)).relation :=
    funext (fun a => funext (fun b => funext (fun x => funext (fun y => relation_prepare p a b x y))))
  have hJ := instance_eq J (normalized (vertices p) (domain p) (constraints p)) he hr
  change J.count = _
  rw [hJ]
  exact count_eq (constraints p) hscope hni

#print axioms prepare_polyT
#print axioms edgeAt_prepare
#print axioms relationAt_prepare
#print axioms valid_prepare_iff
#print axioms count_prepare
end CSPConsequence.SparsePreparation
