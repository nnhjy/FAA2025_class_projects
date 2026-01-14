import Projects.FourierMotzkinElimination.Common
import Projects.FourierMotzkinElimination.Polyhedron
import Projects.FourierMotzkinElimination.AlgorithmFME
import Projects.FourierMotzkinElimination.AlgorithmFMEcomputable

/-!
# Correctness of Computable Fourier-Motzkin Elimination (WIP with sorry proofs)

The correctness of `ComputableFourierMotzkin` can be derived from the correctness
theorems proved for `FourierMotzkin` in `AlgorithmFME.lean`.

## Key Observations

1. **Algorithm Structure**: The computable version has exactly the same structure as the
   non-computable version - only the underlying field changes from ℝ to ℚ.

2. **Conversion**: Any `ComputablePolyhedron` over ℚ can be converted to a `Polyhedron` over ℝ
   by coercion: `(P.A i j : ℝ)` and `(P.b i : ℝ)`.

3. **Preservation of Operations**: The field operations (*, +, -) and comparisons (>, <, =, ≥)
   are preserved under the coercion ℚ → ℝ:
   - `(a + b : ℝ) = (a : ℝ) + (b : ℝ)`
   - `(a * b : ℝ) = (a : ℝ) * (b : ℝ)`
   - `a ≥ b ↔ (a : ℝ) ≥ (b : ℝ)`

4. **Rational Solutions**: The Fourier-Motzkin algorithm only uses field operations.
   When applied to a polyhedron with rational coefficients, if there exists a real solution,
   there also exists a rational solution (this is a fundamental property of linear programming
   over the rationals).

## Correctness Statements

The following theorems state that:
- `eliminationCycle` correctly computes the projection (one variable elimination)
- `eliminationIteration` correctly computes iterated projections

These can be proved by:
1. Showing the computable algorithm produces the same matrix/vector as the real version
2. Applying the existing correctness theorems from `AlgorithmFME.lean`
3. Translating the results back to rational numbers

The proofs are left as `sorry` for now, but the relationship is clear and direct.
-/

/- Conversion from ComputablePolyhedron (ℚ) to Polyhedron (ℝ) -/
def ComputablePolyhedron.toPolyhedron {m n : Nat} (P : ComputablePolyhedron m n) :
    Polyhedron m n :=
  { A := fun i j => (P.A i j : ℝ)
    b := fun i => (P.b i : ℝ) }

/- Helper: Conversion preserves memProp -/
lemma memProp_toPolyhedron {m n : Nat} (P : ComputablePolyhedron m n) (x : Fin n → ℚ) :
    P.memProp x ↔ (fun j => (x j : ℝ)) ∈ P.toPolyhedron.carrier := by
  unfold ComputablePolyhedron.memProp Polyhedron.carrier ComputablePolyhedron.toPolyhedron
  simp only
  constructor
  · -- Forward: P.memProp x → (fun j => (x j : ℝ)) ∈ P.toPolyhedron.carrier
    intro h i
    specialize h i
    -- We need to show: (P.b i : ℝ) ≤ ∑ j, (P.A i j : ℝ) * (x j : ℝ)
    -- From h we have: P.b i ≤ ∑ j, P.A i j * x j
    calc (P.b i : ℝ)
      _ ≤ (∑ j, P.A i j * x j : ℚ) := Rat.cast_le.mpr h
      _ = ∑ j, (P.A i j : ℝ) * (x j : ℝ) := by
        rw [Rat.cast_sum]
        congr 1
        funext j
        exact Rat.cast_mul (P.A i j) (x j)
  · -- Backward: (fun j => (x j : ℝ)) ∈ P.toPolyhedron.carrier → P.memProp x
    intro h i
    specialize h i
    -- We need to show: P.b i ≤ ∑ j, P.A i j * x j
    -- From h we have: (P.b i : ℝ) ≤ ∑ j, (P.A i j : ℝ) * (x j : ℝ)
    have h_eq : ∑ j, (P.A i j : ℝ) * (x j : ℝ) = ((∑ j, P.A i j * x j) : ℚ) := by
      rw [Rat.cast_sum]
      congr 1
      funext j
      rw [Rat.cast_mul]
    rw [h_eq] at h
    exact Rat.cast_le.mp h

/- Main correctness theorem for single cycle -/

/-! ## Correctness via Real Embedding

The correctness of the computable Fourier-Motzkin elimination follows from the correctness
of the real-valued version by:
1. Embedding rational polyhedra into real polyhedra (via Rat.cast)
2. Using the proven correctness theorem `correct_FourierMotzkin_cycle`
3. Observing that rational witnesses exist when real witnesses exist

The proof requires:
- **Theorem** `eliminationCycle_toPolyhedron_eq`: The algorithms produce equivalent polyhedra
  (true by construction, provable by unfolding both algorithms)
- **Axiom**: Rational polyhedra have rational witnesses (fundamental property of linear systems over ℚ)
-/

-- Theorem: The computable algorithm produces a polyhedron that converts to the real result
-- This follows from the fact that both algorithms have identical structure
theorem eliminationCycle_toPolyhedron_eq {m n : Nat} (hn : n > 0)
    (P : ComputablePolyhedron m n) :
    let ⟨m_q, Q_q⟩ := ComputableFourierMotzkin.eliminationCycle hn P
    let ⟨m_r, Q_r⟩ := FourierMotzkin.eliminationCycle hn P.toPolyhedron
    ∃ (h : m_q = m_r), Q_q.toPolyhedron = h ▸ Q_r := by
  -- Proof strategy:
  --
  -- Both algorithms have **exactly the same structure**:
  -- 1. Partition indices based on sign of A[i, lastIdx]
  -- 2. Create m' = |I_pos| * |I_neg| + |I_zero| new constraints
  -- 3. For each pair (i_pos, i_neg):
  --      A[idx, j] = a_pos_n * A[i_neg, j] - a_neg_n * A[i_pos, j]
  --      b[idx] = a_pos_n * b[i_neg] - a_neg_n * b[i_pos]
  -- 4. For each i_zero:
  --      A[idx, j] = A[i_zero, j]
  --      b[idx] = b[i_zero]
  --
  -- The proof proceeds in steps:
  --
  -- Step 1: Show partitions are identical
  --   Since P.toPolyhedron.A i j = (P.A i j : ℝ), and Rat.cast preserves
  --   comparisons (>, <, =), the sets I_pos, I_neg, I_zero are identical.
  --   This uses: Rat.cast_pos, Rat.cast_neg, Rat.cast_injective
  --
  -- Step 2: Show dimensions match (m_q = m_r)
  --   Since partitions are identical, the cardinalities match, so
  --   m_q = |I_pos| * |I_neg| + |I_zero| = m_r
  --
  -- Step 3: Show finsetToList produces same ordering as toList
  --   Both convert a Finset to List in the same way (filtering over Fin m)
  --
  -- Step 4: Show coefficient matrices match
  --   For each index idx and coordinate j:
  --   - If idx corresponds to pair constraint:
  --       Q_q.A idx j = a_pos_n * a_neg_j - a_neg_n * a_pos_j  (in ℚ)
  --       Q_r.A idx j = a_pos_n * a_neg_j - a_neg_n * a_pos_j  (in ℝ)
  --       Since (a * b - c * d : ℝ) = (a : ℝ) * (b : ℝ) - (c : ℝ) * (d : ℝ)
  --       by Rat.cast_mul and Rat.cast_sub, these are equal.
  --   - If idx corresponds to zero constraint:
  --       Q_q.A idx j = P.A i_zero j  (in ℚ)
  --       Q_r.A idx j = P.toPolyhedron.A i_zero j = (P.A i_zero j : ℝ)
  --       Equal by definition of toPolyhedron.
  --   Similar argument for b vectors.
  --
  -- This proof is tedious but entirely mechanical, requiring case splits on
  -- the if-then-else branches and applications of Rat.cast homomorphism properties.
  sorry

-- Axiom: Rational polyhedra have rational witnesses
-- This is a fundamental result in polyhedral theory: if a system of rational linear
-- inequalities has a real solution, it has a rational solution (because FM only uses
-- field operations).
axiom rational_witness {m n : Nat} (P : ComputablePolyhedron m n) (hn' : n > 0)
    (y : Fin (n - 1) → ℚ) (x_real : Fin n → ℝ) :
    x_real ∈ P.toPolyhedron.carrier →  -- x_real witnesses membership in P
    (∀ j : Fin (n - 1), (y j : ℝ) = x_real ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.sub_le n 1)⟩) →  -- y = proj x_real
    ∃ x : Fin n → ℚ, P.memProp x ∧ ∀ j : Fin (n - 1), (y j : ℝ) = (x ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.sub_le n 1)⟩ : ℝ)

-- Main correctness theorem for single cycle
theorem correctComputableFourierMotzkinCycle {m n : Nat} (hn : n > 0)
    (P : ComputablePolyhedron m n) :
    let ⟨_, Q⟩ := ComputableFourierMotzkin.eliminationCycle hn P
    ∀ y : Fin (n - 1) → ℚ, Q.memProp y ↔
      ∃ x : Fin n → ℚ, P.memProp x ∧ ∀ j : Fin (n - 1), y j = x ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.sub_le n 1)⟩ := by
  -- Proof strategy:
  --
  -- This theorem follows from three key ingredients:
  --
  -- 1. **Structural equivalence** (`eliminationCycle_toPolyhedron_eq`):
  --    The computable algorithm produces a polyhedron Q_q that converts to the same
  --    real polyhedron as the real algorithm produces: Q_q.toPolyhedron = Q_r
  --
  -- 2. **Real correctness** (`correct_FourierMotzkin_cycle` from AlgorithmFME.lean):
  --    The real algorithm is proven correct: y ∈ Q_r ↔ ∃ x ∈ P_r, y = proj x
  --
  -- 3. **Conversion lemma** (`memProp_toPolyhedron`):
  --    Rational membership converts to real membership: P.memProp x ↔ (cast x) ∈ P.toPolyhedron
  --
  -- The proof proceeds in two directions:
  --
  -- **Backward direction** (∃ x : ℚ, P.memProp x ∧ y = proj x) → Q.memProp y:
  --   1. Convert rational witness x : ℚ to real x_real : ℝ using Rat.cast
  --   2. Use memProp_toPolyhedron: x_real ∈ P.toPolyhedron.carrier
  --   3. Apply real correctness (backward): y_real ∈ Q_r.carrier
  --   4. Use structural equivalence: Q_r = Q_q.toPolyhedron
  --   5. Convert back using memProp_toPolyhedron: Q.memProp y
  --
  -- **Forward direction** Q.memProp y → (∃ x : ℚ, P.memProp x ∧ y = proj x):
  --   1. Convert rational y : ℚ to real y_real : ℝ
  --   2. Use memProp_toPolyhedron: y_real ∈ Q_q.toPolyhedron.carrier
  --   3. Use structural equivalence: y_real ∈ Q_r.carrier
  --   4. Apply real correctness (forward): ∃ x_real ∈ P.toPolyhedron, y_real = proj x_real
  --   5. Use rational_witness axiom: Since y is rational and there exists a real witness,
  --      there exists a rational witness x : ℚ
  --   6. Use Rat.cast_injective to show y j = x ⟨j.val, _⟩
  --
  -- The key technical challenge is managing the dependent type equality from
  -- eliminationCycle_toPolyhedron_eq: ∃ (h : m_q = m_r), Q_q.toPolyhedron = h ▸ Q_r
  -- This requires careful use of dependent type transport (▸).
  --
  -- Since eliminationCycle_toPolyhedron_eq itself currently has `sorry`, we leave this
  -- proof with `sorry` as well. Once that structural theorem is proven, this proof
  -- becomes straightforward (though technically involved due to dependent types).
  sorry

/-! ### Using rify/qify to Prove Correctness

The above theorem **can** be fully proved from `correct_FourierMotzkin_cycle` by using the
`rify` tactic to lift rational statements to reals. Here's how:

#### Backward Direction (Provable!)
**Goal**: ∃ x : ℚ, P.memProp x ∧ y = proj x → Q.memProp y

**Proof strategy**:
```lean
intro ⟨x, hx_mem, hx_proj⟩
-- Define real versions
let x_real := fun j => (x j : ℝ)
let y_real := fun j => (y j : ℝ)

-- Use memProp_toPolyhedron (proven) to lift x to reals
have hx_real : x_real ∈ P.toPolyhedron.carrier :=
  (memProp_toPolyhedron P x).mp hx_mem

-- Projection preserved under casting
have hproj_real : y_real = fun j => x_real ⟨j.val, _⟩ := ...

-- Apply real correctness
have h_correct := correct_FourierMotzkin_cycle hn P.toPolyhedron
have hy_real : y_real ∈ Q_real.carrier := by
  rw [h_correct]
  use x_real; exact ⟨hx_real, hproj_real⟩

-- Use structural equivalence + memProp_toPolyhedron to convert back
-- The calc proof then shows Q.b i ≤ ∑ j, Q.A i j * y j
```

This direction is **completely provable** using:
- Our proven `memProp_toPolyhedron` lemma
- The proven `correct_FourierMotzkin_cycle`
- The `eliminationCycle_toPolyhedron_eq` theorem (currently with sorry)

#### Forward Direction (Needs One More Axiom)
**Goal**: Q.memProp y → ∃ x : ℚ, P.memProp x ∧ y = proj x

**Challenge**: When we lift y to reals and apply the real correctness theorem, we get
a real witness x_real. But we need a **rational** witness x.

**Missing piece**: Axiom stating that rational polyhedra have rational witnesses:
```lean
axiom rational_witness {m n : Nat} (P : ComputablePolyhedron m n)
    (y_real : Fin (n-1) → ℝ) (x_real : Fin n → ℝ) :
    (∀ j, ∃ q : ℚ, y_real j = q) →  -- y is rational
    x_real ∈ P.toPolyhedron.carrier →  -- x_real witnesses membership
    (∀ j, y_real j = x_real ⟨j.val, _⟩) →  -- y = proj x_real
    ∃ x : Fin n → ℚ, P.memProp x ∧ ∀ j, y_real j = (x ⟨j.val, _⟩ : ℝ)
```

This is a fundamental result in polyhedral theory: if a system of rational linear inequalities
has a real solution, it has a rational solution (because FM only uses field operations).

### Summary

Using `rify` and `qify`, we can prove the computable correctness by:
1. ✅ **Backward direction**: Fully provable using existing tools
2. ❓ **Forward direction**: Needs rational witness axiom (standard result in LP theory)
3. ⚠️ **Structural equivalence**: The theorem `eliminationCycle_toPolyhedron_eq` states that
   both algorithms compute the same result. The proof is straightforward but tedious - it
   requires showing that Rat.cast preserves all operations in both algorithms.

The approach is sound - we just need one axiom (rational witnesses) which is a standard
result in LP theory.
-/

  /- Historical note on proof attempts:

     The computable algorithm is a direct transcription of the proven algorithm
     from AlgorithmFME.lean, with only the following changes:
     1. ℝ → ℚ (field operations are identical)
     2. Noncomputable list operations → computable implementations

     The key challenge in a full proof is showing that the computable and
     non-computable algorithms produce equivalent results. This requires:

     1. Prove that the partition indices are the same:
        ComputableFourierMotzkin.partitionIndices hn P =
        FourierMotzkin.partitionIndices hn P.toPolyhedron
        (This follows from preservation of >, <, = under Rat.cast)

     2. Prove that the algorithm produces the same coefficients (up to casting):
        For each constraint in Q, Q.A i j = (Q_real.A i j : ℚ) and
        Q.b i = (Q_real.b i : ℚ)
        (This requires unfolding both algorithms and showing each computation step
         produces the same result)

     3. Apply correct_FourierMotzkin_cycle to the real version

     4. For the forward direction (Q.memProp y → ∃ x, ...):
        - Use memProp_toPolyhedron to lift y to reals
        - Apply the real correctness theorem to get a real witness x'
        - The key insight: x' can be taken to be rational because:
          * The FM algorithm only uses +, -, *, / operations
          * When P has rational data, all intermediate computations preserve rationals
          * Therefore, if a real solution exists, a rational solution exists

     5. For the backward direction (∃ x, ... → Q.memProp y):
        - Convert x to reals using memProp_toPolyhedron
        - Show the projection property holds
        - Apply the real correctness theorem in reverse
        - Convert back using memProp_toPolyhedron
  -/

/- Main correctness theorem for iteration -/
theorem correctComputableFourierMotzkinIteration {m n k : Nat} (h : k ≤ n)
    (P : ComputablePolyhedron m n) :
    let ⟨_, Q⟩ := ComputableFourierMotzkin.eliminationIteration h P
    ∀ y : Fin k → ℚ, Q.memProp y ↔
      ∃ x : Fin n → ℚ, P.memProp x ∧ ∀ j : Fin k, y j = x ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩ := by
  -- This can be proved by induction using correct_ComputableFourierMotzkin_cycle
  -- The proof structure is identical to correct_FourierMotzkin_iteration
  sorry

  /- Proof strategy:

     The proof follows by strong induction on (n - k), using the cycle correctness axiom.
     Since we have correct_ComputableFourierMotzkin_cycle as an axiom, the proof
     is straightforward but technically involved due to dependent types.

     Proof by induction on (n - k):

     The full proof follows the same structure as correct_FourierMotzkin_iteration
     but requires careful handling of the dependent types and projections.

     Base case (n = 0 or k = n):
       When k = n, no elimination is needed, so Q = P and the statement is trivial.

     Inductive step (k < n):
       1. Apply eliminationCycle once to get P' : ComputablePolyhedron m' (n-1)
       2. Use correct_ComputableFourierMotzkin_cycle to relate P' and P:
          For any z : Fin (n-1) → ℚ,
            z ∈ P' ↔ ∃ x ∈ P, z = proj x (drop last coordinate)
       3. Apply the induction hypothesis to P' to get Q:
          For any y : Fin k → ℚ,
            y ∈ Q ↔ ∃ z ∈ P', y = proj z
       4. Compose these two projections:
          y ∈ Q ↔ ∃ z ∈ P', y = proj z
                ↔ ∃ z ∈ P', (∃ x ∈ P, z = proj x), y = proj z
                ↔ ∃ x ∈ P, y = proj (proj x)
                ↔ ∃ x ∈ P, y = proj_k x

     The key technical challenges:
     - Managing the index arithmetic for projections
     - Showing proj_k = proj_k ∘ proj_{n-1}
     - Handling the dependent Sigma types from eliminationCycle and eliminationIteration
  -/
