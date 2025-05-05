# MST-Lean4

# MSTLean4

**MSTLean4** is a Lean 4 project that formalizes and proves the correctness of classic Minimum Spanning Tree (MST) algorithm, with a focus on Kruskal's algorithm. It is built on top of [Mathlib4](https://github.com/leanprover-community/mathlib4) and designed with modularity in mind to support additional graph algorithms in the future.

---

## 📁 Project Structure

```

MSTLean4/
├── .github/               # GitHub-specific files (e.g. workflows, issue templates)
├── .lake/                 # Lake build system's cache and build artifacts
├── MSTLean4/              # Main Lean source directory
│   ├── DataStructures/    # Core data structures (e.g. Partition ADT, DSU)
│   ├── GraphTheory/       # Formalizations of graphs, trees, and MSTs
│   └── Basic.lean         # Common definitions and helper theorems
├── .gitignore             # Git ignore rules
├── lake-manifest.json     # Lake’s manifest file (auto-generated)
├── lakefile.toml          # Project configuration for the Lake build system
├── lean-toolchain         # Specifies the Lean toolchain version
├── MSTLean4.lean          # Root Lean file that imports project modules
└── README.md              # Project documentation
````


---

## 🚀 Goals

-  Define graphs, subgraphs, trees, and spanning trees formally
-  Implement and prove correctness of naive Kruskal’s algorithm (in progress)
-  Design and implement the Disjoint Set Union (DSU) structure
-  Extend Kruskal’s algorithm using DSU (in progress)
-  Prove correctness of DSU-based Kruskal and implement Prim’s algorithm (in progress)

---

## 🛠 Requirements

- [Lean 4](https://leanprover-community.github.io/get_started.html)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)
- [Lake](https://github.com/leanprover/lake) (Lean's package manager/build tool)

---

## ⚙️ Setup

1. Clone the repository:
   ```bash
   git clone https://github.com/Ayush-GiTHuB-Priyadarshi/MSTLean4.git
   cd MSTLean4

2. Fetch dependencies and build the project:

   ```bash
   lake update
   lake build
   ```

3. Open the project in [VS Code with Lean 4 extension](https://leanprover-community.github.io/get_started.html).


## 📚 Acknowledgements

* *Introduction to Graph Theory* by Douglas B. West  
* *A Walk Through Combinatorics* by Miklós Bóna  
* *Introduction to Algorithms* (CLRS) by Cormen, Leiserson, Rivest, and Stein  
* Built using the Lean 4 proof assistant and Mathlib4


## 📄 License

This project is licensed under the MIT License. See the [LICENSE](./LICENSE) file for details.

