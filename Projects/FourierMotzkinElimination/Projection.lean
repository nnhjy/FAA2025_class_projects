import Projects.FourierMotzkinElimination.Common
import Projects.FourierMotzkinElimination.Polyhedron

import Mathlib.Data.Set.Lattice

/- # Projection machineries
- We work with vectors `x` as functions `Fin n → ℝ`.
  The projection onto the first `k` coordinates is implemented by
  precomposing with `Fin.castLEEmb h : Fin k ↪ Fin n`, available when `h : k ≤ n`.
-/

/- **Definition 1. Projection of vector**
The coordinate projection `π : (Fin n → ℝ) → (Fin k → ℝ)` onto the first `k` coordinates,
defined when `h : k ≤ n`, by precomposition with `Fin.castLEEmb h`. -/
def proj (k n : Nat) (h : k ≤ n) (x : Fin n → ℝ) : Fin k → ℝ :=
  fun i ↦ x ((Fin.castLEEmb h) i)

-- notation: max "π_" k:arg => proj k _ _

/- A lemma about how `proj` acts on coordinates `i`: -/
@[simp]
lemma proj_coords (k n : Nat) (h_le : k ≤ n) (x : Fin n → ℝ) (i : Fin k) :
  proj k n h_le x i = x ((Fin.castLEEmb h_le) i) := rfl

/- **Definition 2. Projection of set**
The projection of a set `S ⊆ ℝ^n` to its first `k` coordinates, `Π_k(S) ⊆ (Fin k → ℝ)`:
`Π_k(S) = { π_k(x) | x ∈ S }`, is its image under the map `proj k n h`, assuming `h : k ≤ n`. -/
def setProj (k n : Nat) (h : k ≤ n) (S : Set (Fin n → ℝ)) : Set (Fin k → ℝ) :=
  { y | ∃ x ∈ S, y = proj k n h x }

/- Membership in terms of coordinates `i`:
  `y ∈ Π_k(S)` iff there exists `x ∈ S` whose first `k` coordinates equal `y`. -/
@[simp]
lemma mem_setProj_iff {k n : Nat} {h_le : k ≤ n} {S : Set (Fin n → ℝ)} {y : Fin k → ℝ} :
  y ∈ setProj k n h_le S
  ↔ ∃ x ∈ S, y = proj k n h_le x := Iff.rfl

/- Membership in terms of coordinates `i`:
  `y ∈ Π_k(S)` iff there exists `x ∈ S` whose first `k` coordinates equal `y`. -/
@[simp]
lemma mem_setProj_iff_coords {k n : Nat} {h_le : k ≤ n} {S : Set (Fin n → ℝ)} {y : Fin k → ℝ} :
  y ∈ setProj k n h_le S
  ↔ ∃ x ∈ S, ∀ i : Fin k, y i = proj k n h_le x i := by
  -- `↔ ∃ x ∈ S, ∀ i : Fin k, y i = x ((Fin.castLEEmb h) i) := by`
  constructor
  · rintro ⟨x, hxS, rfl⟩
    exact ⟨x, hxS, by intro i; rfl⟩
  · rintro ⟨x, hxS, hyx⟩
    refine ⟨x, hxS, ?_⟩
    funext i
    simpa using hyx i

/- **Definition 3. Projection of polyhedron**
  The projection of the feasible set onto the first `k` coordinates.
-/
def polyhedronProj {m n k : Nat} (h : k ≤ n)
  (P : Polyhedron m n) : Set (Fin k → ℝ) := setProj k n h P.carrier

/- `simp`-friendly membership form for the projected feasible set. -/
@[simp]
lemma Polyhedron.mem_projectCarrier_iff {m n k : Nat} {h_le : k ≤ n}
  {P : Polyhedron m n} {y : Fin k → ℝ} :
  y ∈ polyhedronProj h_le P ↔ ∃ x ∈ P.carrier, y = proj k n h_le x := Iff.rfl
