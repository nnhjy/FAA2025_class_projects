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
