import Projects.HuangJY.Common

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Convex.Basic

structure Polyhedron (m n : Nat) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

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

/- # The polyhedron is convex
- For any polyhedron `P`, its `carrier set` is convex in the sense of Mathlib's Convex definition.
- Convexity means: For any two points x, y in the polyhedron and any a, b ≥ 0 with a + b = 1,
  the convex combination a • x + b • y is also in the polyhedron.
-/
theorem polyhedron_is_convex {m n : Nat} (P : Polyhedron m n) :
  Convex ℝ P.carrier := by
  unfold Convex
  intro x hx
  unfold StarConvex
  intro y hy a b ha hb hab
  -- Need to show: a • x + b • y ∈ P.carrier
  unfold Polyhedron.carrier
  intro i
  -- Need to show: ∑ j, P.A i j * (a • x + b • y) j ≥ P.b i
  calc
    ∑ j : Fin n, P.A i j * (a • x + b • y) j
      = ∑ j : Fin n, P.A i j * (a * x j + b * y j) := by simp [Pi.add_apply, Pi.smul_apply]
    _ = ∑ j : Fin n, (P.A i j * (a * x j) + P.A i j * (b * y j)) := by
        congr 1; ext j; ring
    _ = ∑ j : Fin n, P.A i j * (a * x j) + ∑ j : Fin n, P.A i j * (b * y j) := by
        rw [Finset.sum_add_distrib]
    _ = a * ∑ j : Fin n, P.A i j * x j + b * ∑ j : Fin n, P.A i j * y j := by
        congr 1
        · rw [Finset.mul_sum]; congr 1; ext j; ring
        · rw [Finset.mul_sum]; congr 1; ext j; ring
    _ ≥ a * P.b i + b * P.b i := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hx i) ha
        · exact mul_le_mul_of_nonneg_left (hy i) hb
    _ = (a + b) * P.b i := by ring
    _ = P.b i := by rw [hab, one_mul]


/- # Note
- It won't work if we define the `carrier` field with default value
  `carrier : Set (Fin n → ℝ) := { x | ∀ i : Fin m, ∑ j : Fin n, A i j * x j ≥ b i }`
- directly within the `structure Polyhedron`,
  since structure fields are not computed properties,
  but data that must be provided when constructing instances.
- See the `alt` example below.
-/

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
