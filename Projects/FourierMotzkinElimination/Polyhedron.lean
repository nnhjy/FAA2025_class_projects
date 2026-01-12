import Projects.FourierMotzkinElimination.Common

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Convex.Basic

/- A polyhedron in `ℝ^n` described by linear inequalities `A x ≥ b`. -/
structure Polyhedron (m n : Nat) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
/- Feasible set: `{ x | ∀ i, ∑ j, A i j * x j ≥ b i }`. -/
def Polyhedron.carrier {m n : Nat} (P : Polyhedron m n):
  Set (Fin n → ℝ) :=
  { x | ∀ i : Fin m, ∑ j : Fin n, P.A i j * x j ≥ P.b i }
  -- { x | ∀ i : Fin m, (A.mulVec x) i ≤ b i }

#check Polyhedron.carrier

def memPolyhedron {m n : Nat} (P : Polyhedron m n) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin m, ∑ j : Fin n, P.A i j * x j ≥ P.b i

lemma memPolyhedron_iff {m n : ℕ} (P : Polyhedron m n) (x : Fin n → ℝ) :
  memPolyhedron P x ↔ x ∈ P.carrier := by
  simp [memPolyhedron, Polyhedron.carrier]
  -- unfold memPolyhedron
  -- unfold Polyhedron.carrier
  -- rfl

/- # Note
- It won't work if we define the `carrier` field with default value
  `carrier : Set (Fin n → ℝ) := { x | ∀ i : Fin m, ∑ j : Fin n, A i j * x j ≥ b i }`
- directly within the `structure Polyhedron`,
  since structure fields are not computed properties,
  but data that must be provided when constructing instances.
- See an alternative example below.
structure Polyhedron_alt (m n : Nat) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  carrier : Set (Fin n → ℝ)
  carrier_eq : carrier = { x | ∀ i : Fin m, ∑ j : Fin n, A i j * x j ≥ b i }

def memPolyhedron_alt {m n : Nat} (P : Polyhedron_alt m n) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin m, ∑ j : Fin n, P.A i j * x j ≥ P.b i

lemma memPolyhedron_iff_alt {m n : ℕ} (P : Polyhedron_alt m n) (x : Fin n → ℝ) :
  memPolyhedron_alt P x ↔ x ∈ P.carrier := by
  simp [memPolyhedron_alt, Polyhedron_alt.carrier_eq]
-/

/- **Attempt on computable Polyhedron definition**
This should allow:
  - Use `#eval P.mem x` to computably test membership
  - Use `if/then/else` with membership tests in your Fourier-Motzkin implementation
  - Execute the Fourier-Motzkin algorithms and get actual results
-/
structure ComputablePolyhedron (m n : Nat) where
  A : Matrix (Fin m) (Fin n) ℚ
  b : Fin m → ℚ

def ComputablePolyhedron.satisfiesConstraint {m n : Nat}
    (P : ComputablePolyhedron m n) (x : Fin n → ℚ) (i : Fin m) : Bool :=
  decide (∑ j : Fin n, P.A i j * x j ≥ P.b i)

def ComputablePolyhedron.mem {m n : Nat}
    (P : ComputablePolyhedron m n) (x : Fin n → ℚ) : Bool :=
  List.all (List.finRange m) (fun i => P.satisfiesConstraint x i)

def ComputablePolyhedron.memProp {m n : Nat}
    (P : ComputablePolyhedron m n) (x : Fin n → ℚ) : Prop :=
  ∀ i : Fin m, ∑ j : Fin n, P.A i j * x j ≥ P.b i

-- Decidable instance for membership
instance {m n : Nat} (P : ComputablePolyhedron m n) (x : Fin n → ℚ) :
    Decidable (P.memProp x) := by
  unfold ComputablePolyhedron.memProp
  infer_instance

/- Example: A simple 2D polyhedron representing the square [0,1] × [0,1]
   Constraints:
     x₀ ≥ 0  (equivalently: -x₀ ≤ 0, or written as x₀ ≥ 0)
     x₁ ≥ 0
     x₀ ≤ 1  (equivalently: x₀ ≥ -1 doesn't work, we need -x₀ ≥ -1)
     x₁ ≤ 1  (equivalently: -x₁ ≥ -1)
   Written as A x ≥ b:
     [1   0] [x₀]   [0]
     [0   1] [x₁] ≥ [0]
     [-1  0]        [-1]
     [0  -1]        [-1]
-/
def exampleSquare : ComputablePolyhedron 4 2 :=
  { A := !![1, 0; 0, 1; -1, 0; 0, -1]
    b := ![0, 0, -1, -1] }
#eval exampleSquare

-- Test point (1/2, 1/2) - should be inside
def point1 : Fin 2 → ℚ := ![1/2, 1/2]
#eval exampleSquare.mem point1  -- Expected: true

-- Test point (2, 1/2) - should be outside (x₀ > 1)
def point2 : Fin 2 → ℚ := ![2, 1/2]
#eval exampleSquare.mem point2  -- Expected: false

-- Test point (0, 0) - should be on the boundary (inside)
def point3 : Fin 2 → ℚ := ![0, 0]
#eval exampleSquare.mem point3  -- Expected: true

-- Test point (1, 1) - should be on the boundary (inside)
def point4 : Fin 2 → ℚ := ![1, 1]
#eval exampleSquare.mem point4  -- Expected: true

-- Test point (-1/4, 1/2) - should be outside (x₀ < 0)
def point5 : Fin 2 → ℚ := ![-1/4, 1/2]
#eval exampleSquare.mem point5  -- Expected: false
