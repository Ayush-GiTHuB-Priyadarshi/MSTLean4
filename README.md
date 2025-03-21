# MST-Lean4

# Minimal Spanning Trees in Lean 4

## Introduction
This project focuses on the formalization and proof of concepts related to **Minimal Spanning Trees (MSTs)** in **Lean 4**, with implementations of fundamental algorithms such as **Kruskal’s** and **Prim’s algorithms**.

## Graph Theory Basics
### Definition of a Graph
A **graph** \( G \) is defined as a triple consisting of:
- A **vertex set** \( V(G) \)
- An **edge set** \( E(G) \)
- A relation associating each edge with two vertices (which may or may not be distinct).

#### Example:
Given \( V = \{ A, B, C, D \} \) and \( E = \{ (A, B), (B, C), (C, D), (D, A) \} \), the graph can be visualized as:

```
 A --- B
 |     |
 D --- C
```

### Types of Graphs
- A **loop** is an edge where both endpoints are the same.
- **Multiple edges** exist when two vertices share more than one edge.
- A **simple graph** has no loops or multiple edges.
- Two vertices \( u \) and \( v \) are **adjacent** if they share an edge. This is written as \( u \sim v \).

### Paths and Cycles
- A **path** is a sequence of vertices where each consecutive pair is connected by an edge, without repetition.
- A **cycle** is a closed path where the starting and ending vertex are the same.

#### Example of a Path:
```
 A → B → C → D
```
#### Example of a Cycle:
```
 A → B → C → D → A
```

### Connectivity
A graph **G** is **connected** if there exists a path between any two vertices. Otherwise, it is **disconnected**.

A **subgraph** of \( G \) is a graph \( H \) such that:
- \( V(H) \subseteq V(G) \)
- \( E(H) \subseteq E(G) \)

### Walks, Trails, and Paths
- A **walk** is a sequence of vertices and edges where edges may repeat.
- A **trail** is a walk without repeated edges.
- A **path** is a trail where vertices do not repeat, except for cycles.
- A **closed trail** is a trail that starts and ends at the same vertex.

### Graph Properties
- **Degree \( d(v) \)** of a vertex \( v \) is the number of edges incident to it.
- The **order** of a graph is the number of vertices: \( |V(G)| \).
- The **size** of a graph is the number of edges: \( |E(G)| \).

## References
- **Introduction to Graph Theory** – Douglas B. West
- **A Walk Through Combinatorics** – Miklós Bóna

