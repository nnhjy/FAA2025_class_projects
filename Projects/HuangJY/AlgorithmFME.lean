import Projects.HuangJY.Common
import Projects.HuangJY.Polyhedron
import Projects.HuangJY.Projection

/-! # Fourier–Motzkin elimination -/

/- Drops the coordinate `ℓ : Fin (n+1)`:
it maps `Fin n` into `Fin (n+1)` skipping `ℓ`. -/
def dropIndex {n : Nat} (ℓ : Fin (n+1)) : Fin n → Fin (n+1) :=
  Fin.succAbove ℓ

/- Or use the concept of embedding -/
-- def dropIndexEmb {n : Nat} (ℓ : Fin (n+1)) : Fin n ↪ Fin (n+1) :=
--   Fin.succAboveEmb ℓ

namespace FourierMotzkinSet
/- **Fourier-Motzkin Elimination: set output** -/

/- Positive-index set for the column `ℓ`: constraints with `A i ℓ > 0`. -/
def Ipos {m n : Nat} (P : Polyhedron m (n+1)) (ℓ : Fin (n+1)) : Set (Fin m) :=
  { i | 0 < P.A i ℓ }

/- Negative-index set for the column `ℓ`: constraints with `A i ℓ < 0`. -/
def Ineg {m n : Nat} (P : Polyhedron m (n+1)) (ℓ : Fin (n+1)) : Set (Fin m) :=
  { i | P.A i ℓ < 0 }

/- Zero-index set for the column `ℓ`: constraints with `A i ℓ = 0`. -/
def Izero {m n : Nat} (P : Polyhedron m (n+1)) (ℓ : Fin (n+1)) : Set (Fin m) :=
  { i | P.A i ℓ = 0 }

/- The eliminated set `Q ⊆ ℝ^n` obtained by eliminating variable `ℓ : Fin (n+1)`.
This is the standard FME output:
- For every `i0 ∈ I0` (zero coefficient), keep `∑_{j≠ℓ} a_{i0, j} y_j ≥ b_{i0}`.
- For every pair `(i+, i-) ∈ I+ × I-`, require
  `b_{i-}/a_{i-,ℓ} - Σ (a_{i-,j}/a_{i-,ℓ}) y_j ≥ b_{i+}/a_{i+,ℓ} - Σ (a_{i+,j}/a_{i+,ℓ}) y_j`.
-/
def elimIndexSet {m n : Nat} (P : Polyhedron m (n+1)) (ℓ : Fin (n+1)) :
    Set (Fin n → ℝ) :=
  let ι := dropIndex ℓ
  { y |
    -- constraints coming from rows with zero coefficient in `ℓ`
    (∀ i : Fin m, P.A i ℓ = 0 →
        (∑ j : Fin n, P.A i (ι j) * y j) ≥ P.b i) ∧
    -- pairwise constraints from positive + negative rows
    (∀ (iPos iNeg : Fin m),
        0 < P.A iPos ℓ → P.A iNeg ℓ < 0 →
        (P.b iNeg) / (P.A iNeg ℓ)
          - ∑ j : Fin n, (P.A iNeg (ι j)) / (P.A iNeg ℓ) * y j
        ≥
        (P.b iPos) / (P.A iPos ℓ)
          - ∑ j : Fin n, (P.A iPos (ι j)) / (P.A iPos ℓ) * y j) }

/- Specialization: eliminate the **last** coordinate of `ℝ^{n+1}`,
producing a set in `ℝ^n`. -/
def elimLastSet {m n : Nat} (P : Polyhedron m (n+1)) : Set (Fin n → ℝ) :=
  elimIndexSet P (Fin.last (n := n))
  -- Note: `Fin.last` is the index `⟨n, n < n+1⟩`.

end FourierMotzkinSet


namespace FourierMotzkin

/- **Algorithm 1 Step 2: Partition indices based on coefficient of last variable** -/
noncomputable
def partitionIndices {m n : Nat} (hn : n > 0) (P : Polyhedron m n) :
  Finset (Fin m) × Finset (Fin m) × Finset (Fin m) :=
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  let I_pos := Finset.univ.filter (fun i => P.A i lastIdx > 0)
  let I_neg := Finset.univ.filter (fun i => P.A i lastIdx < 0)
  let I_zero := Finset.univ.filter (fun i => P.A i lastIdx = 0)
  (I_pos, I_neg, I_zero)

/- Helper: Embed Fin (n-1) into Fin n for n > 0 -/
def Fin.embedPred {n : Nat} (hn : n > 0) (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, by
    have h1 : i.val < n - 1 := i.isLt
    have h2 : n - 1 < n := Nat.sub_lt hn (by omega)
    exact Nat.lt_trans h1 h2
  ⟩

/- **Fourier-Motzkin Elimination (Algorithm 1): project from n to n-1 dimensions**

  Given polyhedron P in ℝ^n defined by constraints:
    ∑_{j=1}^n a_{ij} x_j ≥ b_i, ∀ i ∈ [m]

  Eliminate variable x_n to obtain polyhedron Q in ℝ^{n-1} defined by:

  (1) For each pair (i₊, i₋) ∈ I₊ × I₋:
      (b_{i₋}/a_{i₋,n} - ∑_{j=1}^{n-1} a_{i₋,j}/a_{i₋,n} · x_j) ≥
      (b_{i₊}/a_{i₊,n} - ∑_{j=1}^{n-1} a_{i₊,j}/a_{i₊,n} · x_j)

      Equivalently: ∑_{j=1}^{n-1} (a_{i₋,j}·a_{i₊,n} - a_{i₊,j}·a_{i₋,n}) x_j ≥
                     b_{i₊}·a_{i₋,n} - b_{i₋}·a_{i₊,n}

  (2) For each i₀ ∈ I₀:
      0 ≥ b_{i₀} - ∑_{j=1}^{n-1} a_{i₀,j} · x_j

      Equivalently: ∑_{j=1}^{n-1} a_{i₀,j} x_j ≥ b_{i₀}
-/
noncomputable
def eleminationCycle {m n : Nat} (hn : n > 0) (P : Polyhedron m n) :
  Σ m' : Nat, Polyhedron m' (n - 1) :=
  let (I_pos, I_neg, I_zero) := partitionIndices hn P
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  let m' := I_pos.card * I_neg.card + I_zero.card

  -- Convert Finsets to lists for indexing
  let posIndices := I_pos.toList
  let negIndices := I_neg.toList
  let zeroIndices := I_zero.toList

  let numPairs := I_pos.card * I_neg.card

  ⟨m', {
    A := fun (idx : Fin m') (j : Fin (n - 1)) =>
      let j' := Fin.embedPred hn j

      if h : idx.val < numPairs then
        -- Pair constraint (i₊, i₋) ∈ I₊ × I₋
        -- Index i₊ = idx.val / |I_neg|, i₋ = idx.val % |I_neg|
        if h_neg_nonempty : I_neg.card > 0 then
          let i_pos_idx := idx.val / I_neg.card
          let i_neg_idx := idx.val % I_neg.card

          if h_pos_valid : i_pos_idx < posIndices.length then
            if h_neg_valid : i_neg_idx < negIndices.length then
              let i_pos := posIndices[i_pos_idx]
              let i_neg := negIndices[i_neg_idx]

              -- Coefficient: a_{i₋,j} · a_{i₊,n} - a_{i₊,j} · a_{i₋,n}
              let a_neg_j := P.A i_neg j'
              let a_pos_j := P.A i_pos j'
              let a_pos_n := P.A i_pos lastIdx
              let a_neg_n := P.A i_neg lastIdx

              a_neg_j * a_pos_n - a_pos_j * a_neg_n
            else 0
          else 0
        else 0
      else
        -- Zero-coefficient constraint from I₀
        let i_zero_idx := idx.val - numPairs
        if h_zero_valid : i_zero_idx < zeroIndices.length then
          let i_zero := zeroIndices[i_zero_idx]
          P.A i_zero j'
        else 0

    b := fun (idx : Fin m') =>
      if h : idx.val < numPairs then
        -- Pair constraint RHS: b_{i₊} · a_{i₋,n} - b_{i₋} · a_{i₊,n}
        if h_neg_nonempty : I_neg.card > 0 then
          let i_pos_idx := idx.val / I_neg.card
          let i_neg_idx := idx.val % I_neg.card

          if h_pos_valid : i_pos_idx < posIndices.length then
            if h_neg_valid : i_neg_idx < negIndices.length then
              let i_pos := posIndices[i_pos_idx]
              let i_neg := negIndices[i_neg_idx]

              let b_pos := P.b i_pos
              let b_neg := P.b i_neg
              let a_pos_n := P.A i_pos lastIdx
              let a_neg_n := P.A i_neg lastIdx

              b_pos * a_neg_n - b_neg * a_pos_n
            else 0
          else 0
        else 0
      else
        -- Zero-coefficient constraint RHS: b_{i₀}
        let i_zero_idx := idx.val - numPairs
        if h_zero_valid : i_zero_idx < zeroIndices.length then
          let i_zero := zeroIndices[i_zero_idx]
          P.b i_zero
        else 0
  }⟩

/- **Iterated Fourier-Motzkin Elimination: project from n to k dimensions** -/
noncomputable
def eleminationIteration {m n k : Nat} (h : k ≤ n) (P : Polyhedron m n) :
  Σ m' : Nat, Polyhedron m' k :=
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
      let ⟨m', P'⟩ := eleminationCycle h_pos P
      eleminationIteration h_le P'
  termination_by n - k

end FourierMotzkin


/- **Correctness theorem for one Fourier-Motzkin elimination cycle (Theorem 1)**

  The carrier of Q equals the projection of P onto the first (n-1) coordinates.
-/
theorem correct_FourierMotzkin_cycle {m n : Nat} (hn : n > 0) (P : Polyhedron m n) :
  let ⟨m', Q⟩ := FourierMotzkin.eleminationCycle hn P
  let h : n - 1 ≤ n := Nat.sub_le n 1
  Q.carrier = polyhedronProj h P := by
  sorry

/- **Correctness theorem for iterated Fourier-Motzkin elimination**

  The carrier of the resulting polyhedron equals the projection of P onto the first k coordinates.
-/
theorem correct_FourierMotzkin_iteration {m n k : Nat} (h : k ≤ n) (P : Polyhedron m n) :
  let ⟨m', Q⟩ := FourierMotzkin.eleminationIteration h P
  Q.carrier = polyhedronProj h P := by
  sorry
