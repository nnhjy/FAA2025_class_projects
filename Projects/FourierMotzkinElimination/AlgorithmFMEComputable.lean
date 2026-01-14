import Projects.FourierMotzkinElimination.Common
import Projects.FourierMotzkinElimination.Polyhedron
import Projects.FourierMotzkinElimination.AlgorithmFME

/- # Computable Fourier–Motzkin Elimination (FME) algorithm

This is a computable version of the Fourier-Motzkin elimination algorithm
that operates on `ComputablePolyhedron` (using rational numbers ℚ instead of ℝ).

The algorithm structure is identical to the non-computable version in AlgorithmFME.lean,
but all operations are computable because ℚ is a computable field.
-/

namespace ComputableFourierMotzkin

/- Helper: Embed Fin (n-1) into Fin n for n > 0 -/
@[simp] def Fin.embedPred {n : Nat} (hn : n > 0) (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, by
    have h1 : i.val < n - 1 := i.isLt
    have h2 : n - 1 < n := Nat.sub_lt hn (by omega)
    exact Nat.lt_trans h1 h2
  ⟩

/- **Indices partition based on coefficient of last variable**

Partitions constraint indices into three sets:
- I_pos: constraints where the coefficient of the last variable is positive
- I_neg: constraints where the coefficient of the last variable is negative
- I_zero: constraints where the coefficient of the last variable is zero
-/
@[simp]
def partitionIndices {m n : Nat} (hn : n > 0) (P : ComputablePolyhedron m n) :
  Finset (Fin m) × Finset (Fin m) × Finset (Fin m) :=
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  let I_pos := Finset.univ.filter (fun i ↦ P.A i lastIdx > 0)
  let I_neg := Finset.univ.filter (fun i ↦ P.A i lastIdx < 0)
  let I_zero := Finset.univ.filter (fun i ↦ P.A i lastIdx = 0)
  (I_pos, I_neg, I_zero)

/- Helper: Convert Finset to List by filtering over all possible indices -/
def finsetToList {m : Nat} (s : Finset (Fin m)) : List (Fin m) :=
  List.finRange m |>.filter (fun i => decide (i ∈ s))

/- **Main step: eliminate xₙ to project from n to n-1 dimensions**

  Given polyhedron P in ℚ^n defined by constraints:
    ∑_{j=1}^n a_{ij} x_j ≥ b_i, ∀ i ∈ [m]

  Eliminate variable x_n to obtain polyhedron Q in ℚ^{n-1} defined by:

  1. For each i₀ ∈ I₀ (zero coefficient in last variable):
      Keep constraint: ∑_{j=1}^{n-1} a_{i₀,j} x_j ≥ b_{i₀}

  2. For each pair (i₊, i₋) ∈ I₊ × I₋:
      Combine constraints to eliminate x_n:
        From i₊: x_n ≤ (b_{i₊} - ∑_{j=1}^{n-1} a_{i₊,j} x_j) / a_{i₊,n}
        From i₋: x_n ≥ (b_{i₋} - ∑_{j=1}^{n-1} a_{i₋,j} x_j) / a_{i₋,n}

      For feasibility, we need:
        (b_{i₋} - ∑_{j=1}^{n-1} a_{i₋,j} x_j) / a_{i₋,n} ≤
        (b_{i₊} - ∑_{j=1}^{n-1} a_{i₊,j} x_j) / a_{i₊,n}

      Multiplying by a_{i₊,n} (positive) and -a_{i₋,n} (positive, since a_{i₋,n} < 0):
        a_{i₊,n} · (b_{i₋} - ∑_{j=1}^{n-1} a_{i₋,j} x_j) ≥
        -a_{i₋,n} · (b_{i₊} - ∑_{j=1}^{n-1} a_{i₊,j} x_j)

      Rearranging:
        ∑_{j=1}^{n-1} (a_{i₊,n} · a_{i₋,j} - a_{i₋,n} · a_{i₊,j}) x_j ≥
        a_{i₊,n} · b_{i₋} - a_{i₋,n} · b_{i₊}
-/
@[simp]
def eliminationCycle {m n : Nat} (hn : n > 0) (P : ComputablePolyhedron m n) :
  Σ m' : Nat, ComputablePolyhedron m' (n - 1) :=
  let (I_pos, I_neg, I_zero) := partitionIndices hn P
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  let m' := I_pos.card * I_neg.card + I_zero.card

  -- Convert Finsets to lists (computable)
  let posIndices := finsetToList I_pos
  let negIndices := finsetToList I_neg
  let zeroIndices := finsetToList I_zero

  let numPairs := I_pos.card * I_neg.card

  ⟨m', {
    A := fun (idx : Fin m') (j : Fin (n - 1)) ↦
      let j' := Fin.embedPred hn j

      if h : idx.val < numPairs then
        -- Pair constraint (i₊, i₋) ∈ I₊ × I₋
        -- Index i₊ = idx.val / |I_neg|, i₋ = idx.val % |I_neg|
        if h_neg_nonempty : I_neg.card > 0 then
          let i_pos_idx := idx.val / I_neg.card
          let i_neg_idx := idx.val % I_neg.card

          if h_pos : i_pos_idx < posIndices.length then
            if h_neg : i_neg_idx < negIndices.length then
              let i_pos := posIndices[i_pos_idx]'h_pos
              let i_neg := negIndices[i_neg_idx]'h_neg
              -- Coefficient: a_{i₊,n} · a_{i₋,j} - a_{i₋,n} · a_{i₊,j}
              let a_neg_j := P.A i_neg j'
              let a_pos_j := P.A i_pos j'
              let a_pos_n := P.A i_pos lastIdx
              let a_neg_n := P.A i_neg lastIdx
              a_pos_n * a_neg_j - a_neg_n * a_pos_j
            else 0
          else 0
        else 0
      else
        -- Zero-coefficient constraint from I₀
        let i_zero_idx := idx.val - numPairs
        if h_zero : i_zero_idx < zeroIndices.length then
          let i_zero := zeroIndices[i_zero_idx]'h_zero
          P.A i_zero j'
        else 0

    b := fun (idx : Fin m') ↦
      if h : idx.val < numPairs then
        -- Pair constraint RHS: a_{i₊,n} · b_{i₋} - a_{i₋,n} · b_{i₊}
        if h_neg_nonempty : I_neg.card > 0 then
          let i_pos_idx := idx.val / I_neg.card
          let i_neg_idx := idx.val % I_neg.card

          if h_pos : i_pos_idx < posIndices.length then
            if h_neg : i_neg_idx < negIndices.length then
              let i_pos := posIndices[i_pos_idx]'h_pos
              let i_neg := negIndices[i_neg_idx]'h_neg
              let b_pos := P.b i_pos
              let b_neg := P.b i_neg
              let a_pos_n := P.A i_pos lastIdx
              let a_neg_n := P.A i_neg lastIdx
              a_pos_n * b_neg - a_neg_n * b_pos
            else 0
          else 0
        else 0
      else
        -- Zero-coefficient constraint RHS: b_{i₀}
        let i_zero_idx := idx.val - numPairs
        if h_zero : i_zero_idx < zeroIndices.length then
          let i_zero := zeroIndices[i_zero_idx]'h_zero
          P.b i_zero
        else 0
  }⟩

/- **Iteration step: project from n to k dimensions**

Repeatedly applies eliminationCycle to project from n dimensions down to k dimensions.
-/
def eliminationIteration {m n k : Nat} (h : k ≤ n) (P : ComputablePolyhedron m n) :
  Σ m' : Nat, ComputablePolyhedron m' k :=
  match n with
  | 0 =>
    have hk : k = 0 := Nat.eq_zero_of_le_zero h
    ⟨m, hk ▸ P⟩
  | n' + 1 =>
    if hk : k = n' + 1 then
      ⟨m, hk ▸ P⟩
    else
      have h_pos : n' + 1 > 0 := by omega
      have h_le : k ≤ n' := by omega
      let ⟨m', P'⟩ := eliminationCycle h_pos P
      eliminationIteration h_le P'
  termination_by n - k

end ComputableFourierMotzkin

/- ## Examples -/

/- Example 1: Eliminate one variable from a 2D square to get a 1D interval

Consider the unit square [0,1] × [0,1] in 2D:
  x₀ ≥ 0, x₁ ≥ 0, x₀ ≤ 1, x₁ ≤ 1

Written as A x ≥ b:
  [1   0] [x₀]   [0]
  [0   1] [x₁] ≥ [0]
  [-1  0]        [-1]
  [0  -1]        [-1]

After eliminating x₁ (the last variable), we should get the projection onto x₀:
  0 ≤ x₀ ≤ 1
-/

def exampleSquare2D : ComputablePolyhedron 4 2 :=
  { A := !![1, 0; 0, 1; -1, 0; 0, -1]
    b := ![0, 0, -1, -1] }

-- Eliminate x₁ to project onto x₀ axis
def projectedInterval :=
  ComputableFourierMotzkin.eliminationCycle (by omega : 2 > 0) exampleSquare2D

#eval projectedInterval.1  -- Number of constraints in projected polyhedron

-- Test that a point in [0,1] satisfies the projected constraints
def testPoint1D : Fin 1 → ℚ := ![1/2]
#eval projectedInterval.2.mem testPoint1D  -- Should be true

def testPoint1D_outside : Fin 1 → ℚ := ![2]
#eval projectedInterval.2.mem testPoint1D_outside  -- Should be false

/- Example 2: Eliminate all variables to check feasibility

A polyhedron is feasible (non-empty) if and only if after eliminating all variables,
the resulting 0-dimensional polyhedron has consistent constraints (no contradiction).
-/

def example3DBox : ComputablePolyhedron 6 3 :=
  { A := !![1, 0, 0; 0, 1, 0; 0, 0, 1; -1, 0, 0; 0, -1, 0; 0, 0, -1]
    b := ![0, 0, 0, -1, -1, -1] }  -- Box [0,1]³

-- Project to 0 dimensions (eliminate all variables)
def feasibilityCheck :=
  ComputableFourierMotzkin.eliminationIteration (by omega : 0 ≤ 3) example3DBox

#eval feasibilityCheck.1  -- Number of constraints (should be able to check if 0 ≥ 0, etc.)

/- Example 3: A simple 3D → 2D projection

Consider a 3D polyhedron and project it onto the first two coordinates.
-/

def example3DPoly : ComputablePolyhedron 3 3 :=
  { A := !![1, 0, 1; 0, 1, 1; 0, 0, -1]  -- x₀ + x₂ ≥ 0, x₁ + x₂ ≥ 0, x₂ ≤ 0
    b := ![0, 0, 0] }

-- Eliminate x₂ (last variable) to project onto (x₀, x₁)
def projected2D :=
  ComputableFourierMotzkin.eliminationCycle (by omega : 3 > 0) example3DPoly

#eval projected2D.1  -- Number of constraints in 2D projection

-- Test a 2D point
def testPoint2D : Fin 2 → ℚ := ![1, 1]
#eval projected2D.2.mem testPoint2D

/- Example 4: Complete iteration - project 3D to 1D -/

def projected1D_from3D :=
  ComputableFourierMotzkin.eliminationIteration (by omega : 1 ≤ 3) example3DBox

#eval projected1D_from3D.1  -- Number of constraints
#eval projected1D_from3D.2.mem ![1/2]  -- Test point in projected space
