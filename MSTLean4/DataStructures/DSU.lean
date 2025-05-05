import Mathlib
import Batteries

-- Here we verify the types for converting between List and Array
#check Array.toList  -- Array α → List α
#check List.toArray  -- List α → Array α

-- Example demonstrating how to convert a List to an Array and back
def exampleConversion : IO Unit := do
  let myList := [1, 2, 3, 4, 5]
  let mut myArray := myList.toArray
  IO.println s!"List to Array: {myArray}"      -- prints: #[1, 2, 3, 4, 5]
  let backToList := myArray.toList
  IO.println s!"Array back to List: {backToList}"  -- prints: [1, 2, 3, 4, 5]

#eval exampleConversion


namespace UnionFind

-- Create an example Union-Find forest (as an Array of UFNode: (parent, rank))
-- Node i has parent and rank as specified
def exampleUF : Array Batteries.UFNode :=
  Array.mk [⟨0, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩]
  -- Index 0: parent = 0, rank = 1     (root)
  -- Index 1: parent = 0, rank = 0     (child of 0)
  -- Index 2: parent = 2, rank = 1     (another root)
  -- Index 3: parent = 2, rank = 0     (child of 2)
  -- Indices 4, 5: not explicitly defined — default behavior used

-- Test: Find parent of each node using `parentD`
#eval Batteries.UnionFind.parentD UnionFind.exampleUF 0  -- → 0
-- Case: Node is its own parent → root of a component

#eval Batteries.UnionFind.parentD UnionFind.exampleUF 1  -- → 0
-- Case: Node 1 is child of 0 → returns its parent

#eval Batteries.UnionFind.parentD UnionFind.exampleUF 2  -- → 2
-- Case: Another root node → parent = self

#eval Batteries.UnionFind.parentD UnionFind.exampleUF 3  -- → 2
-- Case: Node 3 is child of 2 → returns its parent

#eval Batteries.UnionFind.parentD UnionFind.exampleUF 4  -- → 4
-- Case: Node not in array → treated as singleton set, parent = self

#eval Batteries.UnionFind.parentD UnionFind.exampleUF 5  -- → 5
-- Case: Same as above → treated as singleton, default parent = self


-- Test: Get rank of each node using `rankD`
#eval Batteries.UnionFind.rankD UnionFind.exampleUF 0  -- → 1
-- Case: Rank of root node 0

#eval Batteries.UnionFind.rankD UnionFind.exampleUF 1  -- → 0
-- Case: Rank of child node 1

#eval Batteries.UnionFind.rankD UnionFind.exampleUF 2  -- → 1
-- Case: Rank of second root node 2

#eval Batteries.UnionFind.rankD UnionFind.exampleUF 3  -- → 0
-- Case: Rank of child node 3

#eval Batteries.UnionFind.rankD UnionFind.exampleUF 4  -- → 0
-- Case: Node not in array → default rank = 0

#eval Batteries.UnionFind.rankD UnionFind.exampleUF 5  -- → 0
-- Case: Same as above → default rank = 0

---------------------------------------------------------------------------------------------------

-- Another demonstration: Convert an Array of (Nat × Nat) pairs to a List
def exampleConversion' : IO Unit := do
  let myArray : Array (Nat × Nat) := Array.mk [(0, 1), (0, 0), (2, 1), (2, 0)]
  IO.println s!"List to Array: {myArray}"        -- prints: #[(0,1), (0,0), (2,1), (2,0)]
  let backToList := myArray.toList
  IO.println s!"Array back to List: {backToList}"  -- prints: [(0,1), (0,0), (2,1), (2,0)]

#eval exampleConversion'


-- Initialize an array representing the Union-Find parent-rank structure.
-- Each element is a pair: (parent, rank)
def KruskalListInitializer (n : Nat) : IO Unit := do
  -- Create a list of n elements: (i, 0) means each node is its own parent, with rank 0
  let myList := List.range n |>.map (λ i => (i , 0))
  IO.println s!"Initialized List: {myList}"  -- Prints list
  let myArray := myList.toArray               -- Convert list to array for UFNode
  IO.println s!"List to Array: {myArray}"     -- Prints array

#eval KruskalListInitializer 5

------------------------------------------------------------------------------------------------------

-- Find the root of the node at a given index using path traversal
-- Implements a basic version of the "find" function in Union-Find
def RootFinder (n : Nat) (idx : {idx : Nat // idx ≤ n}) : IO Unit := do
  -- Create the same initial list: disjoint singleton sets with rank 0
  let myList := List.range n |>.map (λ i => (i , 0))
  IO.println s!"Initialized List: {myList}"
  let myArray := myList.toArray
  IO.println s!"List to Array: {myArray}"

  let count := myArray.size
  let mut current := idx.val                -- Start from the given index
  let mut counter := count                  -- Use counter to avoid infinite loops in malformed data

  while counter > 0 do
    let parent := myArray[current]!.fst     -- Get the parent of the current node
    if parent == current then
      -- Found the root (node is its own parent)
      IO.println s!"Root found: {current}"
      return
    current := parent                       -- Move one level up
    counter := counter - 1

  -- Fallback in case we failed to find a root within count iterations
  IO.println "Counter reached zero before finding root."

#eval RootFinder 5 (⟨3, by decide⟩ : {idx : Nat // idx ≤ 5})
--This should print "Root found 3" since 3 is its own parent in the initialized array

-----------------------------------------------------------------------------------------------------

-- Perform union of the sets containing idx1 and idx2
-- Implements "union by rank" logic without path compression
def RootUnion (n : Nat) (idx1 : {idx : Nat // idx ≤ n}) (idx2 : {idx : Nat // idx ≤ n}) : IO Unit := do
  -- Step 1: Initialize parent-rank array
  let myList := List.range n |>.map (λ i => (i , 0))
  IO.println s!"Initialized List: {myList}"
  let mut myArray := myList.toArray
  IO.println s!"List to Array: {myArray}"

  let count := myArray.size
  let mut current1 := idx1.val
  let mut current2 := idx2.val
  let mut counter := count

  -- Step 2: Find roots of idx1 and idx2 by traversing parent pointers
  while counter > 0 do
    let parent1 := myArray[current1]!.fst
    let parent2 := myArray[current2]!.fst
    if parent1 == parent2 then
      -- If roots are the same, they're in the same set
      IO.println s!"Both indices are in the same set: {parent1}"
      return
    current1 := parent1
    current2 := parent2
    counter := counter - 1

  -- Step 3: If the loop breaks, we assume current1 and current2 are roots (or same)
  IO.println "Counter reached zero before finding root."

  -- Redundant root check after loop, for safety
  if current1 == current2 then
    IO.println s!"Both indices are in the same set: {current1}"
  else
    -- Step 4: Perform union by rank
    let rank1 := myArray[current1]!.snd
    let rank2 := myArray[current2]!.snd

    if rank1 < rank2 then
      -- Attach the tree with smaller rank under the one with larger rank
      myArray := myArray.set! current1 (current2, rank1)
      IO.println s!"Merged {current1} into {current2}"
    else if rank1 > rank2 then
      myArray := myArray.set! current2 (current1, rank2)
      IO.println s!"Merged {current2} into {current1}"
    else
      -- If ranks are equal, pick one root and increment its rank
      myArray := myArray.set! current2 (current1, rank2)
      myArray := myArray.set! current1 (current1, rank1 + 1)
      IO.println s!"Merged {current2} into {current1}"

    -- Final debug output of the updated parent-rank array
    IO.println s!"Updated Array: {myArray}"

#eval RootUnion 5 (⟨3, by decide⟩ : {idx : Nat // idx ≤ 5}) (⟨4, by decide⟩ : {idx : Nat // idx ≤ 5})
-- As 4 is merged into 3, the output should show the updated array with 4's parent as 3 and rank of 3 incremented.

---------------------------------------------------------------------------------------------------------

-- General-purpose root finder for Union-Find (Disjoint Set Union).
-- Given an array of (parent, rank) and an index, returns the root index.
-- No path compression is done here.
def RootFinderGeneral (arr : Array (Nat × Nat)) (idx : Nat) : IO Nat := do
  -- Boundary check
  if idx >= arr.size then
    IO.println "Error: Index out of bounds."
    return idx

  let count := arr.size
  let mut current := idx
  let mut counter := count    -- Prevent infinite loops in malformed data

  while counter > 0 do
    let parent := arr[current]!.fst
    if parent == current then
      -- Found the root of the set
      IO.println s!"Root found: {current}"
      return current
    current := parent
    counter := counter - 1

  -- In case the loop ends without finding a root
  IO.println "Counter reached zero before finding root."
  return current

--------------------------------------------------------------------------------------------------------

-- General-purpose union operation for Union-Find.
-- Given an array (parent, rank) and two indices, merges their sets using union by rank.
-- Updates are local to this function and not persisted unless explicitly returned.
def RootMergerGeneral (arr : Array (Nat × Nat)) (idx1 : Nat) (idx2 : Nat) : IO Unit := do
  -- Boundary check for indices
  if idx1 >= arr.size || idx2 >= arr.size then
    IO.println "Error: Index out of bounds."
    return

  let count := arr.size
  let mut current1 := idx1
  let mut current2 := idx2
  let mut counter := count
  let mut Arr := arr   -- Mutable copy to apply changes

  -- Step 1: Try to find roots of idx1 and idx2
  while counter > 0 do
    let parent1 := arr[current1]!.fst
    let parent2 := arr[current2]!.fst
    if parent1 == parent2 then
      -- Same root => already in the same set
      IO.println s!"Both indices are in the same set: {parent1}"
      return
    current1 := parent1
    current2 := parent2
    counter := counter - 1

  -- Step 2: Fallback if loop exits early
  IO.println "Counter reached zero before finding root."

  if current1 == current2 then
    -- Redundant check for set equality
    IO.println s!"Both indices are in the same set: {current1}"
  else
    -- Step 3: Union by rank
    let rank1 := arr[current1]!.snd
    let rank2 := arr[current2]!.snd

    if rank1 < rank2 then
      -- Attach lower-rank root under higher-rank root
      Arr := Arr.set! current1 (current2, rank1)
      IO.println s!"Merged {current1} into {current2}"
    else if rank1 > rank2 then
      Arr := Arr.set! current2 (current1, rank2)
      IO.println s!"Merged {current2} into {current1}"
    else
      -- If ranks are equal, pick one root and increment its rank
      Arr := arr.set! current2 (current1, rank2)
      Arr := arr.set! current1 (current1, rank1 + 1)
      IO.println s!"Merged {current2} into {current1}"

    -- Final debug print of the updated structure
    IO.println s!"Updated Array: {Arr}"

-- Our initial Union-Find array, where each element is a pair (parent, rank)
-- Index:  0      1      2      3
-- Value: (0,1) (0,0) (2,1) (2,0)
-- Meaning:
-- - Node 0 is its own parent, rank 1 (root of its set)
-- - Node 1's parent is 0, rank 0
-- - Node 2 is its own parent, rank 1 (root of another set)
-- - Node 3's parent is 2, rank 0

-------------------------------------------------------------------------

def exampleUF' : Array (Nat × Nat) := Array.mk [(0, 1), (0, 0), (2, 1), (2, 0)]

/-
  Visual structure:

  Set 1:
      0
     /
    1

  Set 2:
      2
     /
    3
-/

-- Find root of node 3
-- Path: 3 → 2 → 2 (stop, since parent == current)
-- Root is 2
#eval RootFinderGeneral exampleUF' 3  -- → 2 Root found: 2

-- Find root of node 2
-- Already root (parent == current), so root is 2
#eval RootFinderGeneral exampleUF' 2  -- → 2 Root found: 2

-- Find root of node 1
-- Path: 1 → 0 → 0 (stop)
-- Root is 0
#eval RootFinderGeneral exampleUF' 1  -- → 0 Root found: 0

-- Find root of node 0
-- Already root (parent == current), so root is 0
#eval RootFinderGeneral exampleUF' 0  -- → 0 Root found: 0

-- Index 4 is out of bounds (array has size 4)
#eval RootFinderGeneral exampleUF' 4  -- → 4 Error: Index out of bounds.

-------------------------------------------------------------------------------

-- Merge nodes 3 and 2
-- Roots: 3 → 2, 2 → 2 → both have same root
-- No merge needed, already in same set
#eval RootMergerGeneral exampleUF' 3 2  -- Both indices are in the same set: 2

-- Merge nodes 3 and 4
-- Error: 4 is out of bounds
#eval RootMergerGeneral exampleUF' 3 4  -- Error: Index out of bounds.

-- Merge nodes 3 and 1
-- Roots: 3 → 2, 1 → 0
-- Different sets, root(3)=2, root(1)=0
-- Ranks: rank(2)=1, rank(0)=1 → Equal
-- Merge by making 0 point to 2 and incrementing rank of 2
-- Updated structure:
--   Arr[0] = (2, 1)  -- 0 now points to 2
--   Arr[2] = (2, 2)  -- rank of 2 increases
-- Final structure:
--     2
--    / \
--   0   3
--  /
-- 1
#eval RootMergerGeneral exampleUF' 3 1  -- Merged 0 into 2

-- Merge nodes 0 and 2
-- New structure from previous operation:
--   - root(0) = 2, root(2) = 2 → already same set
-- BUT if we re-evaluate from original array:
--   - root(0) = 0, root(2) = 2 → different
-- Ranks: rank(0)=1, rank(2)=1 → Equal
-- Merge 2 into 0 and increment rank of 0
-- Updated:
--   Arr[2] = (0, 1)
--   Arr[0] = (0, 2)
-- Final structure:
--     0
--    / \
--   1   2
--        \
--         3
#eval RootMergerGeneral exampleUF' 0 2  -- Merged 2 into 0

---------------------------------------------------------------------------------------------------

-- ===============================
-- Graph Structures and DSU Basics
-- ===============================

-- A simple Graph structure using natural numbers for vertices
structure Graph where
  vertices : List Nat                  -- List of vertex identifiers (e.g., [0, 1, 2])
  edges : List (Nat × Nat)            -- List of undirected edges as pairs (u, v)
  deriving Repr                       -- Automatically derive a string representation

-- Alternative version of a Graph using bounded natural numbers (Fin n)
structure Graph' where
  vertices : List (Fin n)             -- Vertices as finite types bounded by `n`
  edges : List (Fin n × Fin n)        -- Edges as pairs of `Fin n` elements

-- ======================================
-- Assumption About Graph Validity
-- ======================================

/-
IMPORTANT ASSUMPTION:
---------------------

We assume in **good faith** that every vertex mentioned in the edge list of the graph
is also present in the vertex list. That is, if an edge (u, v) appears in `graph.edges`,
then both `u` and `v` are guaranteed to be in `graph.vertices`.

⚠️ This implementation **does not perform** any checks to enforce this condition.

Example of a valid graph:
  vertices := [0, 1, 2]
  edges    := [(0, 1), (1, 2)]   -- OK: all nodes are listed in `vertices`

Example of an invalid graph (which we assume does NOT occur):
  vertices := [0, 1]
  edges    := [(0, 1), (1, 2)]   -- ❌ Error in logic: 2 is not in `vertices`

Also, we cannot verify if (u,v) and (v,u) are both present in the edge list.
  This is a directed graph, and we assume it is undirected.
  We assume that the edges are undirected and that each edge appears only once.
  This means that if (u, v) is in the edge list, (v, u) should not be present.
In a verified setting (e.g., using dependent types), we would ensure this invariant
by construction or prove it explicitly. But here, for simplicity and performance,
we assume that the inputs are well-formed.
-/


-- ======================================
-- Example Graph and DSU Initialization
-- ======================================

-- An example graph with 5 vertices (0 through 4) and 5 edges forming a cycle
def exampleGraph : Graph :=
  {
    vertices := [0, 1, 2, 3, 4],                          -- Nodes labeled 0 to 4
    edges := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]     -- Edges forming a cycle
  }

-- Converts a Graph's vertex list into a DSU-like structure:
-- Each vertex is initially its own parent, and rank is 0
def VerticesToInitialDSU (graph : Graph) : IO Unit := do
  let vertices := graph.vertices                          -- Extract vertex list
  let myList := vertices.map (λ v => (v, 0))              -- Create (parent, rank) tuples
  IO.println s!"Initialized List: {myList}"               -- Print initial list
  let myArray := myList.toArray                           -- Convert to array for constant-time access
  IO.println s!"List to Array: {myArray}"                 -- Print the array form

-- =============================
-- Assigning Weights to Edges
-- =============================

-- Given a weight function `w` on edges, produce a list of weights
def EdgeWeight (graph : Graph) (w : (Nat × Nat) → Nat) : List Nat :=
  graph.edges.map w                                       -- Map the weight function over the edge list

-- Example usage:
-- `EdgeWeight exampleGraph (λ (u, v) => u + v)`
-- would produce: [1, 3, 5, 7, 4]

-- A custom function to find the element `x` in a non-empty list that minimizes `f x`
def List.minBy (l : List α) (f : α → Nat) (h : l ≠ []) : α :=
  match l with
  | x :: xs =>
    match p:xs with
    | [] => x
    | y :: ys =>
      let tailMin := List.minBy (y :: ys) f (by simp [p])
      if f x < f tailMin then
        x
      else
        tailMin

-- ===================================
-- Visual Example / Debug Reference
-- ===================================
/-
exampleGraph:
Vertices: [0, 1, 2, 3, 4]
Edges:
  (0, 1)
  (1, 2)
  (2, 3)
  (3, 4)
  (4, 0)

This forms a cycle:
     0
   /   \
  4     1
   \   /
     3 - 2

VerticesToInitialDSU will print:
Initialized List: [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)]
List to Array:    [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)]

-/
-- ===================================


-- def Kruskal (graph : Graph') (w : (Nat × Nat) → Nat) : IO (List (Nat × Nat)) := do
--   let vertices := graph.vertices
--   let edges := graph.edges
--   let n := vertices.length
--   let m := edges.length
--   let mut count := 0
--   let mut mst : List (Nat × Nat) := []
--   let myList := vertices.map (λ v => (v, 0))
--   let mut myArray := myList.toArray
--   while count < m  do
--     count := count + 1
--     let edges := edges.filter (λ e => e ∈ graph.edges)
--     let leastWtEdge := if edges ≠ [] then
--       some (List.minBy (λ e => w e) edges)
--     else
--       none
--     match leastWtEdge with
--     | some edge =>
--       let u := edge.fst
--       let v := edge.snd
--       if RootFinderGeneral myArray u = RootFinderGeneral myArray v then
--         IO.println s!"Both indices are in the same set: {u}"
--       else
--         RootMergerGeneral myArray u v
--         mst := edge :: mst
--         count := count + 1
--         IO.println s!"Added edge: {edge}"
--     | none =>
--       IO.println "No more edges to process."
--       break
--   IO.println s!"Final MST: {mst}"
--   return mst

-- ========================
-- Minimal Edge Function
-- ========================

/--
`MinimalEdge` finds the edge with the minimum weight in a given list of edges.
It takes a list of edges `edges` and a weight function `w` to determine the weight of each edge.
- If the list is empty, it prints a message and returns a default value `(0, 0)`.
- Otherwise, it finds the edge with the minimal weight using the `List.minBy` function.
- Returns the edge with the minimum weight.
-/
def MinimalEdge (edges : List (Nat × Nat)) (w : (Nat × Nat) → Nat) : IO (Nat × Nat) :=
  if edges.isEmpty then                               -- Check if the list of edges is empty
    do
      IO.println "No edges to process."              -- Print message
      return (0, 0)                                   -- Return a default value when no edges are available
  else
    do
      match edges with
      | [] =>
        IO.println "No edges to process."            -- In case of an empty list (just to handle exhaustively)
        return (0, 0)                                 -- Default return value
      | _ =>
        let leastWtEdge := List.minBy edges w (sorry) -- Find the edge with the minimal weight using `List.minBy`.
        -- `sorry` is used as a placeholder here for Lean's inability to automatically prove that the list is non-empty.
        IO.println s!"Minimal edge: {leastWtEdge}"    -- Print the minimal edge found
        return leastWtEdge                             -- Return the minimal edge

-- =========================
-- Kruskal's Algorithm
-- =========================

/--
`Kruskal` is an implementation of Kruskal's algorithm for finding the Minimum Spanning Tree (MST) of a graph.
It takes the list of vertices, edges, and a weight function `w` for the edges as input.
- The function performs the following:
  - Initializes each vertex as its own root (parent) with a rank of `0`.
  - Iterates over the edges (after sorting them based on the weight function `w`).
  - For each edge, finds the roots of the two vertices. If they are in the same set, it skips the edge.
  - Otherwise, it merges the sets containing the two vertices, and adds the edge to the MST.
  - The function returns the list of edges included in the MST.
  - During the process, intermediate steps are printed for debugging purposes.
-/
noncomputable def Kruskal (vertices : List Nat) (edges : List (Nat × Nat)) (w : (Nat × Nat) → Nat) : IO (List (Nat × Nat)) := do
  let n := vertices.length           -- Get the number of vertices
  let m := edges.length              -- Get the number of edges
  let mut count := 0                 -- Initialize edge counter
  let mut mst : List (Nat × Nat) := [] -- Initialize empty MST list
  let myList := vertices.map (λ v => (v, 0))  -- Initialize each vertex with itself as the root and rank 0
  let mut myArray := myList.toArray  -- Convert the list to an array for efficient access

  -- Start iterating through all the edges
  while count < m do
    count := count + 1                            -- Increment the counter (this is the number of processed edges)
    let leastWtEdge ← MinimalEdge edges w        -- Find the edge with the minimum weight
    let (u, v) := leastWtEdge                    -- Destructure the edge into its vertices `u` and `v`
    let rootU ← RootFinderGeneral myArray u      -- Find the root of vertex `u`
    let rootV ← RootFinderGeneral myArray v      -- Find the root of vertex `v`

    -- If both vertices have the same root, they are already in the same set (no cycle)
    if rootU == rootV then
      IO.println s!"Both indices are in the same set: {rootU}"   -- Print that the edge would form a cycle and won't be added
    else
      RootMergerGeneral myArray u v               -- Union the two sets of vertices `u` and `v`
      mst := leastWtEdge :: mst                   -- Add the edge to the MST list
      IO.println s!"Added edge: {leastWtEdge}"     -- Print the edge added to the MST

  IO.println s!"Final MST: {mst}"                    -- Print the final MST after processing all edges
  return mst                                          -- Return the MST

-- ============================
-- Why the `noncomputable` annotation?
-- ============================
/-
The `Kruskal` function is marked as `noncomputable` because it involves using certain functions that are not guaranteed to be computable in Lean. Specifically:
- Lean's core logic does not automatically resolve the execution of certain I/O-based actions like `IO.println` and `List.minBy` when they are combined with user-provided functions like the weight function `w` (which may not always be computable).
- Lean cannot automatically compute values when dealing with functions marked as `sorry` (i.e., placeholders for proofs), such as in the `MinimalEdge` function.

By marking `Kruskal` as `noncomputable`, we are telling Lean to allow the execution of this function even though it contains computations that are not computable in the logical sense.
-/
