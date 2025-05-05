import Mathlib

variable {V : Type} [Fintype V] [DecidableEq V] [Inhabited V]

namespace SimpleGraph

#check SimpleGraph

#check Path

#check Walk

#check Subgraph

#check support

#moogle "A graph G is connected if there is a path between every pair of vertices."

#check Connected

-- def IsAcyclic : Prop := ∀ ⦃v : V⦄ (c : G.Walk v v), ¬c.IsCycle
#check IsAcyclic

#moogle "defining a minimal connected graph."
#leansearch "Definition of a minimal connected tree."

#moogle "G is minimal connected graph with n vertices then following are equivalent,
G is minimal connected then removing any edge from G will disconnect G and G does not contain any cycle."

def MinimalConnected (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ e : Sym2 V, e ∈ G.edgeSet → ¬ (G.deleteEdges {e}).Connected

#check MinimalConnected

#moogle "Checking if a graph has a cycle."
#check SimpleGraph.IsAcyclic

def Theorem_minimal_connected_iff_acyclic (G : SimpleGraph V) : MinimalConnected G ↔ G.IsAcyclic := by
    constructor
    -- Forward direction: MinimalConnected G → G.IsAcyclic
    intro hG
    by_contra hC
    push_neg at hC
    have ⟨v, h⟩ := not_forall.mp hC
    obtain ⟨c, hc⟩ := not_forall.mp h
    have hC : c.IsCycle := not_not.mp hc
    have hGc : ∀ e ∈ c.edges.toFinset, (G.deleteEdges {e}).Connected :=
      fun e he => by sorry
    sorry
    -- Backward direction: G.IsAcyclic → MinimalConnected G
    intro hC
    sorry

#moogle "A graph is a tree if it is connected and acyclic."

#check SimpleGraph.IsTree

/-
structure SimpleGraph.IsTree.{u} {V : Type u} (G : SimpleGraph V) : Prop
number of parameters: 2
fields:
  SimpleGraph.IsTree.isConnected : G.Connected
  SimpleGraph.IsTree.IsAcyclic : G.IsAcyclic
constructor:
  SimpleGraph.IsTree.mk.{u} {V : Type u} {G : SimpleGraph V} (isConnected : G.Connected) (IsAcyclic : G.IsAcyclic) :
    G.IsTree
-/
#print IsTree

lemma tree_iff_unique_path (G : SimpleGraph V) :
  G.IsTree ↔ ∀ (x y : V), ∃! (p : G.Walk x y), p.IsPath := by
  sorry

def Leaf (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] : Prop :=
    G.degree v = 1

#moogle "length of a path is the number of edges in the path."
#check SimpleGraph.Walk.length

lemma tree_has_two_leaves {T : SimpleGraph V} [Fintype V] (hT : T.IsTree) (hV : Fintype.card V ≥ 2) [∀ v, Fintype (T.neighborSet v)] :
  ∃ v w : V, v ≠ w ∧ Leaf T v ∧ Leaf T w := by
  sorry
  
theorem tree_edges_count {T : SimpleGraph V} [Fintype V] (hT : T.IsTree) [Fintype T.edgeSet] :
  Fintype.card T.edgeSet = Fintype.card V - 1 := by
  sorry

#moogle "In a simple graph the number of edges are finite."
#check SimpleGraph.mem_edgeFinset

/-
theorem SimpleGraph.mem_edgeFinset.{u_1} : ∀ {V : Type u_1} {G : SimpleGraph V} {e : Sym2 V}
  [inst : Fintype ↑G.edgeSet], e ∈ G.edgeFinset ↔ e ∈ G.edgeSet :=
fun {V} {G} {e} [Fintype ↑G.edgeSet] ↦ Set.mem_toFinset
-/
#print SimpleGraph.mem_edgeFinset

/--
warning: automatically included section variable(s) unused in theorem 'SimpleGraph.edgeFinset_eq_edgeSet':
  [Fintype V]
  [DecidableEq V]
  [Inhabited V]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [Fintype V] [DecidableEq V] [Inhabited V] in theorem ...
note: this linter can be disabled with `set_option linter.unusedSectionVars false`
-/
#guard_msgs in
theorem edgeFinset_eq_edgeSet {G : SimpleGraph V} [Fintype G.edgeSet] :
  G.edgeFinset = G.edgeSet.toFinset := by
  ext e
  rw [SimpleGraph.mem_edgeFinset]


theorem connected_graph_with_n_minus_1_edges_is_tree {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
  (hG : G.Connected) (hE : G.edgeFinset.card = Fintype.card V - 1) : G.IsTree := by
  sorry

end SimpleGraph
