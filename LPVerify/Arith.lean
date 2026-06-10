/-
  Rat / Array arithmetic and Bool-to-Prop lemmas used by the soundness
  proofs in `LP.Verify.Sound`. The verifier is Mathlib-free, so
  this file fills the small gaps between core Lean 4 and what the
  soundness layer needs: Rat helpers, array size/index lemmas, sparse
  bilinear identities, and the per-checker Bool→Prop bridges.
-/
module

public import LPVerify.Bool
public import LPVerify.Prop

@[expose] public section

namespace LP.Verify

open LP

/-- Bridge: `v.toArray[i]!` (Array `get!` on the underlying array)
    equals `v[i]!` (Vector `get!`). Stated with the Array form on
    the LHS so `@[simp]` *removes* `.toArray` insertions, normalizing
    everything to Vector form. Without this bridge, soundness proofs
    that mix `Vector`-typed structure fields with `.toArray`-converted
    intermediates leave `simp`/`rw` looking at `match decidableGetElem?
    …` vs `Array.get!Internal …` mismatches that block destructuring. -/
@[simp] theorem _root_.Vector.toArray_getElem! {α} [Inhabited α] {n : Nat}
    (v : Vector α n) (i : Nat) : v.toArray[i]! = v[i]! := by
  by_cases h : i < n
  · rw [getElem!_pos v i h, getElem!_pos v.toArray i (by rw [Vector.size_toArray]; exact h)]
    rfl
  · rw [getElem!_neg v i h, getElem!_neg v.toArray i (by rw [Vector.size_toArray]; exact h)]

/-! ## Derived `Rat` arithmetic. Small gaps over core Lean 4, namespaced
  under `RatAux` to keep the public verifier surface clean. -/

namespace RatAux

/-- Combine `add_le_add_left` and `add_le_add_right`. -/
protected theorem add_le_add {a b c d : Rat} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr h₁) (Rat.add_le_add_left.mpr h₂)

/-- `0 ≤ a − b ↔ b ≤ a`. Reorientation of `Rat.le_iff_sub_nonneg`. -/
protected theorem sub_nonneg {a b : Rat} : 0 ≤ a - b ↔ b ≤ a :=
  (Rat.le_iff_sub_nonneg b a).symm

/-- Monotonicity of subtraction. -/
protected theorem sub_le_sub {a b c d : Rat} (h₁ : a ≤ b) (h₂ : d ≤ c) :
    a - c ≤ b - d := by
  have : a + (-c) ≤ b + (-d) := RatAux.add_le_add h₁ (Rat.neg_le_neg h₂)
  simpa [Rat.sub_eq_add_neg] using this

end RatAux

/-! ## `Nat.all` / `Nat.fold` loop bridges.

  The executable checkers loop with `Nat.all` / `Nat.fold` (compiled
  to allocation-free tail-recursive loops via their `@[csimp]`
  companions). These two lemmas convert the loops back to the shapes
  the soundness layer reasons about: a bounded `∀` for `Nat.all`, and
  the `Array.range` folds (which `range_fold_mono` and friends in
  `LP.Verify.Sound` are stated against) for `Nat.fold`. -/

/-- `Nat.all n f = true` iff `f` holds at every index below `n`. -/
theorem natAll_eq_true : ∀ {n : Nat} {f : (i : Nat) → i < n → Bool},
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  intro n
  induction n with
  | zero =>
      intro f
      simp
  | succ n ih =>
      intro f
      rw [Nat.all_succ, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h₁, h₂⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
        · exact h₁ i h
        · exact h₂
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

/-- A `Nat.fold` whose step ignores the index bound is the matching
    `Array.range` fold. -/
theorem natFold_eq_range_foldl {α : Type u} (n : Nat) (step : α → Nat → α)
    (init : α) :
    Nat.fold n (fun i _ acc => step acc i) init =
      (Array.range n).foldl step init := by
  induction n with
  | zero =>
      simp [Array.range_eq_range']
  | succ n ih =>
      rw [Nat.fold_succ, ih, Array.range_succ]
      simp

/-! ## Bool-to-Prop lemmas.

  Each lemma is a single-direction `Bool = true → Prop fact`. The
  Prop targets live in `LP.Verify.Prop`; the soundness proofs
  in `LP.Verify.Sound` consume these bridges. -/

theorem boundCombinationPos_imp {m n : Nat} {p : Problem m n} {d : DualBundle m n}
    (h : boundCombinationPos p d = true) :
    0 < dualBoundCombination p d := by
  unfold boundCombinationPos at h
  exact of_decide_eq_true h

/-- `(!o.isNone || decide P) = true ↔ (o = none → P)`. The Bool
    pattern used in `dualNonnegAndZeroWhereAbsent` for the
    zero-where-absent clauses. -/
private theorem or_not_isNone_decide_eq_true {α} {o : Option α} {P : Prop}
    [Decidable P] (h : (!o.isNone || decide P) = true) :
    o = none → P := by
  intro hNone
  rw [Bool.or_eq_true] at h
  rcases h with hSome | hP
  · simp [hNone] at hSome
  · exact of_decide_eq_true hP

theorem dualNonnegAndZeroWhereAbsent_imp
    {m n : Nat} {p : Problem m n} {d : DualBundle m n}
    (h : dualNonnegAndZeroWhereAbsent p d = true) :
    DualNonnegZeroWhereAbsent p d := by
  unfold dualNonnegAndZeroWhereAbsent at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hRow, hCol⟩ := h
  rw [natAll_eq_true] at hRow hCol
  refine
    { row_nonneg := ?_
      col_nonneg := ?_
      row_zero_absent := ?_
      col_zero_absent := ?_ }
  · intro i
    have hi' := hRow i.val i.isLt
    simp only [Bool.and_eq_true] at hi'
    exact ⟨of_decide_eq_true hi'.1.1.1, of_decide_eq_true hi'.1.1.2⟩
  · intro j
    have hj' := hCol j.val j.isLt
    simp only [Bool.and_eq_true] at hj'
    exact ⟨of_decide_eq_true hj'.1.1.1, of_decide_eq_true hj'.1.1.2⟩
  · intro i
    have hi' := hRow i.val i.isLt
    simp only [Bool.and_eq_true] at hi'
    exact ⟨or_not_isNone_decide_eq_true hi'.1.2,
           or_not_isNone_decide_eq_true hi'.2⟩
  · intro j
    have hj' := hCol j.val j.isLt
    simp only [Bool.and_eq_true] at hj'
    exact ⟨or_not_isNone_decide_eq_true hj'.1.2,
           or_not_isNone_decide_eq_true hj'.2⟩

/-! ## Size lemmas for `arraySub`.

  Size lemmas for sparse matrix evaluation live in `LP.Verify.Bool`
  alongside the Bool-level operations they describe. -/

theorem arraySub_size_of_eq (a b : Array Rat) (h : a.size = b.size) :
    (arraySub a b).size = a.size := by
  unfold arraySub
  rw [if_pos h, Array.size_zipWith, h, Nat.min_self]

/-- `arraySub a b` at index `i` is `a[i]! - b[i]!`, given sizes match
    and `i` is in range. -/
theorem arraySub_get!_of_eq
    (a b : Array Rat) (h : a.size = b.size) (i : Nat) (hi : i < a.size) :
    (arraySub a b)[i]! = a[i]! - b[i]! := by
  have hib : i < b.size := h ▸ hi
  have hZip : i < (Array.zipWith (fun x y => x - y) a b).size := by
    rw [Array.size_zipWith]
    exact Nat.lt_min.mpr ⟨hi, hib⟩
  unfold arraySub
  rw [if_pos h]
  rw [getElem!_pos (Array.zipWith (fun x y => x - y) a b) i hZip]
  rw [Array.getElem_zipWith]
  rw [← getElem!_pos a i hi, ← getElem!_pos b i hib]

/-! ## Vector-lifted analogues of `dot` / `evalATy`.

  The proof obligations that the Array versions need (size match,
  in-range index, output-size lemma) come for free when the inputs
  are `Vector`-typed: sizes are part of the type. These bridges
  connect the two views so the executable checkers can use the fused
  Vector forms without rewriting every soundness lemma. -/

/-- `vDot` agrees with `dot` on the underlying arrays — the Vector
    form has no size-mismatch fallback, but on equally-sized inputs
    they compute the same sum. -/
theorem vDot_eq_dot {n : Nat} (a b : Vector Rat n) :
    vDot a b = dot a.toArray b.toArray := by
  unfold vDot dot
  rw [if_pos (by rw [a.size_toArray, b.size_toArray])]
  rw [a.size_toArray]

/-- `vPrimalObj` agrees with `primalObj` on the underlying array. -/
theorem vPrimalObj_eq_primalObj {m n : Nat} (p : Problem m n) (x : Vector Rat n) :
    vPrimalObj p x = primalObj p x.toArray := by
  unfold vPrimalObj primalObj
  rw [vDot_eq_dot]

/-- The fused scatter `evalATySub` agrees with `evalATy` applied to
    the explicit difference vector. The soundness layer keeps its
    statements in `evalATy`/`arraySub` form; this bridge lets the
    Bool-to-Prop lemmas for `isStationary` / `isFarkasFeasible`
    rewrite the executable form away. -/
theorem evalATySub_eq {m n : Nat} (p : Problem m n) (yL yU : Vector Rat m) :
    evalATySub p yL yU = evalATy p (arraySub yL.toArray yU.toArray) := by
  unfold evalATySub evalATy
  have hfun : applyATySub yL yU =
      applyATy (m := m) (n := n) (arraySub yL.toArray yU.toArray) := by
    funext out entry
    obtain ⟨r, c, v⟩ := entry
    show (if h : c.val < out.size then
            out.set c.val (out[c.val]! + v * (yL[r] - yU[r])) h
          else out) =
         (if h : c.val < out.size then
            out.set c.val (out[c.val]! +
              v * (arraySub yL.toArray yU.toArray)[r.val]!) h
          else out)
    rw [arraySub_get!_of_eq yL.toArray yU.toArray
      (by rw [yL.size_toArray, yU.size_toArray])
      r.val (by rw [yL.size_toArray]; exact r.isLt)]
    simp only [Vector.toArray_getElem!]
    rw [getElem!_pos yL r.val r.isLt, getElem!_pos yU r.val r.isLt]
    simp only [Fin.getElem_fin]
  rw [hfun]

/-! ## Sparse bilinear identity.

  Core Lean does not expose the Mathlib-style finite-sum API used for
  dot-product update lemmas, so we use small Nat-indexed prefix sums
  and connect them to the executable `Array.foldl` definitions. -/

private def dotPrefix (a b : Array Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => dotPrefix a b n + a[n]! * b[n]!

private def sparsePrefix {m n : Nat} (entries : Array (Fin m × Fin n × Rat))
    (y x : Array Rat) : Nat → Rat
  | 0 => 0
  | k + 1 =>
      match entries[k]? with
      | some e => sparsePrefix entries y x k + e.2.2 * y[e.1.val]! * x[e.2.1.val]!
      | none => sparsePrefix entries y x k

private def sparseBilinear {m n : Nat} (p : Problem m n) (y x : Array Rat) : Rat :=
  p.a.foldl (fun acc e => acc + e.2.2 * y[e.1.val]! * x[e.2.1.val]!) 0

private theorem dotFold_eq_dotPrefix (a b : Array Rat) (k : Nat) :
    dotFold a b k = dotPrefix a b k := by
  induction k with
  | zero => simp [dotFold, dotPrefix]
  | succ k ih =>
      unfold dotFold at ih ⊢
      rw [Nat.fold_succ, ih]
      rfl

private theorem dot_eq_dotPrefix
    (a b : Array Rat) (h : a.size = b.size) :
    dot a b = dotPrefix a b a.size := by
  unfold dot
  rw [if_pos h]
  exact dotFold_eq_dotPrefix a b a.size

private theorem dotPrefix_set_within
    (y a : Array Rat) (r : Nat) (v : Rat) (hr : r < a.size)
    (hSize : y.size = a.size) (n : Nat) (hn : n ≤ a.size) :
    dotPrefix y (a.set r v hr) n =
      dotPrefix y a n + if r < n then y[r]! * (v - a[r]!) else 0 := by
  induction n with
  | zero =>
      simp [dotPrefix, Rat.add_zero]
  | succ n ih =>
      by_cases hrn : r = n
      · subst r
        have hnLt : n < a.size := hr
        have hnSet : n < (a.set n v hr).size := by
          rw [Array.size_set]
          exact hr
        have hnY : n < y.size := by rw [hSize]; exact hnLt
        rw [dotPrefix, ih (by omega)]
        rw [getElem!_pos (a.set n v hr) n hnSet]
        rw [Array.getElem_set]
        rw [if_pos rfl]
        have hnn : ¬ n < n := by omega
        have hnns : n < n + 1 := by omega
        simp [hnn, hnns]
        rw [show dotPrefix y a (n + 1) = dotPrefix y a n + y[n]! * a[n]! by rfl]
        rw [getElem!_pos y n hnY, getElem!_pos a n hnLt]
        change dotPrefix y a n + 0 + y[n] * v =
          (dotPrefix y a n + y[n] * a[n]) + y[n] * (v - a[n])
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg,
          Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
      · by_cases hrLtN : r < n
        · have hnLt : n < a.size := by omega
          have hnSet : n < (a.set r v hr).size := by
            rw [Array.size_set]
            exact hnLt
          have hnY : n < y.size := by rw [hSize]; exact hnLt
          rw [dotPrefix, ih (by omega)]
          rw [getElem!_pos (a.set r v hr) n hnSet]
          rw [Array.getElem_set]
          simp [hrn, hrLtN, Nat.lt_succ_of_lt hrLtN]
          rw [dotPrefix]
          rw [getElem!_pos y n hnY, getElem!_pos a n hnLt]
          grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
        · have hrNotLtSucc : ¬ r < n + 1 := by omega
          have hnLt : n < a.size := by omega
          have hnSet : n < (a.set r v hr).size := by
            rw [Array.size_set]
            exact hnLt
          have hnY : n < y.size := by rw [hSize]; exact hnLt
          rw [dotPrefix, ih (by omega)]
          rw [getElem!_pos (a.set r v hr) n hnSet]
          rw [Array.getElem_set]
          simp [hrLtN, hrNotLtSucc]
          rw [dotPrefix]
          rw [getElem!_pos y n hnY, getElem!_pos a n hnLt]
          simp [hrn, Rat.add_zero]

private theorem dotPrefix_set
    (y a : Array Rat) (r : Nat) (v : Rat) (hr : r < a.size)
    (hSize : y.size = a.size) :
    dotPrefix y (a.set r v hr) a.size =
      dotPrefix y a a.size + y[r]! * (v - a[r]!) := by
  rw [dotPrefix_set_within y a r v hr hSize a.size (Nat.le_refl _)]
  simp [hr]

private theorem dot_set
    (y a : Array Rat) (r : Nat) (v : Rat) (hr : r < a.size)
    (hSize : y.size = a.size) :
    dot y (a.set r v hr) =
      dot y a + y[r]! * (v - a[r]!) := by
  have hSetSize : y.size = (a.set r v hr).size := by
    rw [Array.size_set]
    exact hSize
  rw [dot_eq_dotPrefix y (a.set r v hr) hSetSize]
  rw [dot_eq_dotPrefix y a hSize]
  rw [hSize]
  exact dotPrefix_set y a r v hr hSize

private theorem dotPrefix_comm_within
    (a b : Array Rat) :
    ∀ n, n ≤ a.size → n ≤ b.size → dotPrefix a b n = dotPrefix b a n
  | 0, _, _ => by simp [dotPrefix]
  | n + 1, hna, hnb => by
      have hna' : n ≤ a.size := by omega
      have hnb' : n ≤ b.size := by omega
      have hia : n < a.size := by omega
      have hib : n < b.size := by omega
      rw [dotPrefix, dotPrefix, dotPrefix_comm_within a b n hna' hnb']
      rw [getElem!_pos a n hia, getElem!_pos b n hib]
      grind [Rat.mul_comm]

private theorem dot_comm
    (a b : Array Rat) (h : a.size = b.size) :
    dot a b = dot b a := by
  rw [dot_eq_dotPrefix a b h, dot_eq_dotPrefix b a h.symm]
  rw [show b.size = a.size from h.symm]
  exact dotPrefix_comm_within a b a.size (Nat.le_refl _) (by rw [← h]; exact Nat.le_refl _)

private theorem dot_set_left
    (a x : Array Rat) (r : Nat) (v : Rat) (hr : r < a.size)
    (hSize : a.size = x.size) :
    dot (a.set r v hr) x =
      dot a x + x[r]! * (v - a[r]!) := by
  have hSetSize : (a.set r v hr).size = x.size := by
    rw [Array.size_set]
    exact hSize
  rw [dot_comm (a.set r v hr) x hSetSize]
  rw [dot_set x a r v hr hSize.symm]
  rw [dot_comm a x hSize]

private theorem dotPrefix_replicate_right_zero (y : Array Rat) (n : Nat) :
    ∀ k, k ≤ n → dotPrefix y (Array.replicate n 0) k = 0
  | 0, _ => rfl
  | k + 1, hk => by
      rw [show dotPrefix y (Array.replicate n 0) (k + 1) =
            dotPrefix y (Array.replicate n 0) k +
              y[k]! * (Array.replicate n (0 : Rat))[k]! from rfl]
      rw [dotPrefix_replicate_right_zero y n k (by omega)]
      rw [getElem!_pos (Array.replicate n (0 : Rat)) k
        (by rw [Array.size_replicate]; omega)]
      rw [Array.getElem_replicate]
      rw [Rat.mul_zero, Rat.zero_add]

private theorem dot_replicate_right_zero (y : Array Rat) (n : Nat)
    (h : y.size = n) :
    dot y (Array.replicate n 0) = 0 := by
  rw [dot_eq_dotPrefix y (Array.replicate n 0) (by simp [h])]
  rw [h]
  exact dotPrefix_replicate_right_zero y n n (Nat.le_refl _)

private theorem dot_replicate_left_zero (x : Array Rat) (n : Nat)
    (h : x.size = n) :
    dot (Array.replicate n 0) x = 0 := by
  rw [dot_comm (Array.replicate n (0 : Rat)) x (by simp [h])]
  exact dot_replicate_right_zero x n h

private theorem dotPrefix_eq_range_fold
    (a b : Array Rat) :
    ∀ n, n ≤ a.size → n ≤ b.size →
      dotPrefix a b n =
        (Array.range n).foldl (fun acc i => acc + a[i]! * b[i]!) 0
  | 0, _, _ => by simp [Array.range_eq_range', dotPrefix]
  | n + 1, hna, hnb => by
      have hna' : n ≤ a.size := by omega
      have hnb' : n ≤ b.size := by omega
      have hia : n < a.size := by omega
      have hib : n < b.size := by omega
      rw [dotPrefix, dotPrefix_eq_range_fold a b n hna' hnb']
      have hRange :
          Array.range (n + 1) = (Array.range n).push n := by
        exact Array.range_succ
      rw [hRange, Array.foldl_push]

theorem dot_eq_range_fold
    (a b : Array Rat) (h : a.size = b.size) :
    dot a b =
      (Array.range a.size).foldl (fun acc i => acc + a[i]! * b[i]!) 0 := by
  rw [dot_eq_dotPrefix a b h]
  exact dotPrefix_eq_range_fold a b a.size (Nat.le_refl _) (by rw [h]; exact Nat.le_refl _)

/-! ## Pointwise affine rays.

  These helpers support the unboundedness proof: `addSmul x λ r` is
  the executable point `x + λ • r`, with linearity facts for dot
  products, objectives, and `evalAx`. -/

def Array.addSmul (x : Array Rat) (lam : Rat) (r : Array Rat) : Array Rat :=
  if x.size = r.size then Array.zipWith (fun xj rj => xj + lam * rj) x r else #[]

theorem Array.addSmul_size_of_eq
    (x r : Array Rat) (lam : Rat) (h : x.size = r.size) :
    (Array.addSmul x lam r).size = x.size := by
  unfold Array.addSmul
  rw [if_pos h, Array.size_zipWith, h, Nat.min_self]

theorem Array.addSmul_get!_of_eq
    (x r : Array Rat) (lam : Rat) (h : x.size = r.size)
    (i : Nat) (hi : i < x.size) :
    (Array.addSmul x lam r)[i]! = x[i]! + lam * r[i]! := by
  have hir : i < r.size := h ▸ hi
  have hZip : i < (Array.zipWith (fun xj rj => xj + lam * rj) x r).size := by
    rw [Array.size_zipWith]
    exact Nat.lt_min.mpr ⟨hi, hir⟩
  unfold Array.addSmul
  rw [if_pos h]
  rw [getElem!_pos (Array.zipWith (fun xj rj => xj + lam * rj) x r) i hZip]
  rw [Array.getElem_zipWith]
  rw [← getElem!_pos x i hi, ← getElem!_pos r i hir]

private theorem range_fold_congr
    (n : Nat) (f g : Nat → Rat)
    (h : ∀ i, i < n → f i = g i) :
    (Array.range n).foldl (fun acc i => acc + f i) 0 =
      (Array.range n).foldl (fun acc i => acc + g i) 0 := by
  apply Rat.le_antisymm
  · induction n with
    | zero =>
        simp [Array.range_eq_range']
    | succ n ih =>
        simp [Array.range_succ]
        exact RatAux.add_le_add
          (by simpa using ih (by intro i hi; exact h i (by omega)))
          (by rw [h n (by omega)]; exact Rat.le_refl)
  · induction n with
    | zero =>
        simp [Array.range_eq_range']
    | succ n ih =>
        simp [Array.range_succ]
        exact RatAux.add_le_add
          (by simpa using ih (by intro i hi; rw [h i (by omega)]))
          (by rw [h n (by omega)]; exact Rat.le_refl)

private theorem range_fold_add
    (n : Nat) (f g : Nat → Rat) :
    (Array.range n).foldl (fun acc i => acc + (f i + g i)) 0 =
      (Array.range n).foldl (fun acc i => acc + f i) 0 +
        (Array.range n).foldl (fun acc i => acc + g i) 0 := by
  induction n with
  | zero =>
      simp [Array.range_eq_range', Rat.zero_add]
  | succ n ih =>
      simp [Array.range_succ]
      have ih' :
          Array.foldl (fun acc i => acc + (f i + g i)) 0 (Array.range n) 0 n =
            Array.foldl (fun acc i => acc + f i) 0 (Array.range n) 0 n +
              Array.foldl (fun acc i => acc + g i) 0 (Array.range n) 0 n := by
        simpa using ih
      rw [ih']
      grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem range_fold_smul
    (n : Nat) (lam : Rat) (f : Nat → Rat) :
    (Array.range n).foldl (fun acc i => acc + lam * f i) 0 =
      lam * (Array.range n).foldl (fun acc i => acc + f i) 0 := by
  induction n with
  | zero =>
      simp [Array.range_eq_range']
  | succ n ih =>
      simp [Array.range_succ]
      have ih' :
          Array.foldl (fun acc i => acc + lam * f i) 0 (Array.range n) 0 n =
            lam * Array.foldl (fun acc i => acc + f i) 0 (Array.range n) 0 n := by
        simpa using ih
      rw [ih']
      grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem dot_addSmul_right
    (c x r : Array Rat) (lam : Rat)
    (hcx : c.size = x.size) (hxr : x.size = r.size) :
    dot c (Array.addSmul x lam r) = dot c x + lam * dot c r := by
  have hySize : (Array.addSmul x lam r).size = x.size :=
    Array.addSmul_size_of_eq x r lam hxr
  rw [dot_eq_range_fold c (Array.addSmul x lam r) (by rw [hySize]; exact hcx)]
  rw [dot_eq_range_fold c x hcx]
  rw [dot_eq_range_fold c r (by rw [← hxr]; exact hcx)]
  rw [hcx]
  calc
    (Array.range x.size).foldl
        (fun acc i => acc + c[i]! * (Array.addSmul x lam r)[i]!) 0
        =
      (Array.range x.size).foldl
        (fun acc i => acc + (c[i]! * x[i]! + c[i]! * (lam * r[i]!))) 0 := by
          apply range_fold_congr
          intro i hi
          rw [Array.addSmul_get!_of_eq x r lam hxr i hi]
          grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
    _ =
      (Array.range x.size).foldl (fun acc i => acc + c[i]! * x[i]!) 0 +
        (Array.range x.size).foldl (fun acc i => acc + c[i]! * (lam * r[i]!)) 0 := by
          exact range_fold_add x.size
            (fun i => c[i]! * x[i]!)
            (fun i => c[i]! * (lam * r[i]!))
    _ =
      (Array.range x.size).foldl (fun acc i => acc + c[i]! * x[i]!) 0 +
        lam * (Array.range x.size).foldl (fun acc i => acc + c[i]! * r[i]!) 0 := by
          have hScale :
              (Array.range x.size).foldl
                  (fun acc i => acc + c[i]! * (lam * r[i]!)) 0 =
                (Array.range x.size).foldl
                  (fun acc i => acc + lam * (c[i]! * r[i]!)) 0 := by
            apply range_fold_congr
            intro i hi
            grind [Rat.mul_assoc, Rat.mul_comm]
          rw [hScale]
          rw [range_fold_smul x.size lam (fun i => c[i]! * r[i]!)]

private def unitVector (n i : Nat) : Array Rat :=
  Array.ofFn (fun j : Fin n => if j.val = i then 1 else 0)

private theorem unitVector_size (n i : Nat) :
    (unitVector n i).size = n := by
  unfold unitVector
  simp

private theorem unitVector_get! (n i j : Nat) (hj : j < n) :
    (unitVector n i)[j]! = if j = i then 1 else 0 := by
  unfold unitVector
  rw [getElem!_pos _ j (by simpa using hj)]
  rw [Array.getElem_ofFn]

private theorem range_fold_unit_zero_before
    (n i : Nat) (a : Array Rat) (hn : n ≤ i) :
    (Array.range n).foldl
      (fun acc j => acc + (if j = i then (1 : Rat) else 0) * a[j]!) 0 = 0 := by
  induction n with
  | zero =>
      simp [Array.range_eq_range']
  | succ n ih =>
      simp [Array.range_succ]
      have hni : n ≠ i := by omega
      have ih' :
          Array.foldl (fun acc j => acc + (if j = i then (1 : Rat) else 0) * a[j]!)
            0 (Array.range n) 0 n = 0 := by
        simpa using ih (by omega)
      rw [ih']
      simp [hni, Rat.zero_add]

private theorem range_fold_unit_get
    (n i : Nat) (a : Array Rat) (hi : i < n) :
    (Array.range n).foldl
      (fun acc j => acc + (if j = i then (1 : Rat) else 0) * a[j]!) 0 = a[i]! := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      simp [Array.range_succ]
      by_cases hin : i = n
      · subst i
        have hzero :
            Array.foldl (fun acc j => acc + (if j = n then (1 : Rat) else 0) * a[j]!)
              0 (Array.range n) 0 n = 0 := by
          simpa using range_fold_unit_zero_before n n a (Nat.le_refl _)
        rw [hzero]
        simp [Rat.zero_add]
      · have hiPrev : i < n := by omega
        have ih' :
            Array.foldl (fun acc j => acc + (if j = i then (1 : Rat) else 0) * a[j]!)
              0 (Array.range n) 0 n = a[i]! := by
          simpa using ih hiPrev
        rw [ih']
        have hni : n ≠ i := by omega
        simp [hni, Rat.add_zero]

private theorem dot_unitVector_left
    (a : Array Rat) (n i : Nat) (ha : a.size = n) (hi : i < n) :
    dot (unitVector n i) a = a[i]! := by
  rw [dot_eq_range_fold (unitVector n i) a (by rw [unitVector_size, ha])]
  rw [unitVector_size]
  apply Eq.trans ?_ (range_fold_unit_get n i a hi)
  apply range_fold_congr
  intro j hj
  rw [unitVector_get! n i j hj]

theorem primalObj_addSmul
    {m n : Nat} (p : Problem m n) (x r : Array Rat) (lam : Rat)
    (hcx : p.c.toArray.size = x.size) (hxr : x.size = r.size) :
    primalObj p (Array.addSmul x lam r) =
      primalObj p x + lam * dot p.c.toArray r := by
  unfold primalObj
  rw [dot_addSmul_right p.c.toArray x r lam hcx hxr]
  grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem dot_replicate_left_zero'
    (x : Array Rat) (n : Nat) (h : x.size = n) :
    dot (Array.replicate n 0) x = 0 :=
  dot_replicate_left_zero x n h

theorem dot_replicate_right_zero'
    (y : Array Rat) (n : Nat) (h : y.size = n) :
    dot y (Array.replicate n 0) = 0 :=
  dot_replicate_right_zero y n h

private theorem sparseBilinear_eq_sparsePrefix
    {m n : Nat} (p : Problem m n) (y x : Array Rat) :
    sparseBilinear p y x = sparsePrefix p.a y x p.a.size := by
  unfold sparseBilinear
  refine Array.foldl_induction
    (as := p.a)
    (motive := fun i acc => acc = sparsePrefix p.a y x i) ?_ ?_
  · rfl
  · intro i acc hAcc
    rw [hAcc]
    rw [sparsePrefix]
    simp [i.isLt]

private theorem dot_evalAx_eq_sparseBilinear
    {m n : Nat} (p : Problem m n) (y x : Array Rat)
    (hY : y.size = m)
    (hX : x.size = n) :
    dot y (evalAx p x) = sparseBilinear p y x := by
  unfold evalAx
  rw [sparseBilinear_eq_sparsePrefix]
  have hFold := Array.foldl_induction
    (as := p.a)
    (init := Array.replicate m 0)
    (f := applyAx x)
    (motive := fun i out =>
      out.size = m ∧ dot y out = sparsePrefix p.a y x i)
    (by
      constructor
      · simp
      · rw [dot_replicate_right_zero y m hY]
        rfl)
    (by
      intro i out hAcc
      obtain ⟨hOutSize, hDot⟩ := hAcc
      cases hEntryEq : p.a[i.val] with
      | mk r cv =>
      cases cv with
    | mk c v =>
    have hrOut : r.val < out.size := by rw [hOutSize]; exact r.isLt
    have hcX : c.val < x.size := by rw [hX]; exact c.isLt
    constructor
    · rw [applyAx_size, hOutSize]
    · unfold applyAx
      simp [hrOut]
      rw [dot_set y out r.val (out[r.val] + v * x[c.val]!) hrOut (by rw [hOutSize]; exact hY)]
      rw [hDot]
      rw [sparsePrefix]
      simp [i.isLt, hEntryEq]
      rw [← getElem!_pos out r.val hrOut]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm])
  exact hFold.2

private theorem dot_evalATy_eq_sparseBilinear
    {m n : Nat} (p : Problem m n) (y x : Array Rat)
    (hY : y.size = m)
    (hX : x.size = n) :
    dot (evalATy p y) x = sparseBilinear p y x := by
  unfold evalATy
  rw [sparseBilinear_eq_sparsePrefix]
  have hFold := Array.foldl_induction
    (as := p.a)
    (init := Array.replicate n 0)
    (f := applyATy y)
    (motive := fun i out =>
      out.size = n ∧ dot out x = sparsePrefix p.a y x i)
    (by
      constructor
      · simp
      · rw [dot_replicate_left_zero x n hX]
        rfl)
    (by
      intro i out hAcc
      obtain ⟨hOutSize, hDot⟩ := hAcc
      cases hEntryEq : p.a[i.val] with
      | mk r cv =>
      cases cv with
    | mk c v =>
    have hcOut : c.val < out.size := by rw [hOutSize]; exact c.isLt
    have hrY : r.val < y.size := by rw [hY]; exact r.isLt
    constructor
    · rw [applyATy_size, hOutSize]
    · unfold applyATy
      simp [hcOut]
      rw [dot_set_left out x c.val (out[c.val] + v * y[r.val]!) hcOut (by rw [hOutSize, ← hX])]
      rw [hDot]
      rw [sparsePrefix]
      simp [i.isLt, hEntryEq]
      rw [← getElem!_pos out c.val hcOut]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm])
  exact hFold.2

theorem dot_y_evalAx_eq_dot_evalATy_x
    {m n : Nat} (p : Problem m n) (y x : Array Rat)
    (hY : y.size = m)
    (hX : x.size = n) :
    dot y (evalAx p x) = dot (evalATy p y) x := by
  rw [dot_evalAx_eq_sparseBilinear p y x hY hX,
      dot_evalATy_eq_sparseBilinear p y x hY hX]


theorem evalAx_addSmul_get!
    {m n : Nat} (p : Problem m n) (x r : Array Rat) (lam : Rat)
    (hx : x.size = n) (hr : r.size = n)
    (i : Nat) (hi : i < m) :
    (evalAx p (Array.addSmul x lam r))[i]! =
      (evalAx p x)[i]! + lam * (evalAx p r)[i]! := by
  let e := unitVector m i
  have heSize : e.size = m := unitVector_size m i
  have hySize : (Array.addSmul x lam r).size = n := by
    have h := Array.addSmul_size_of_eq x r lam (by rw [hx, hr])
    rw [hx] at h
    exact h
  have hLeft :
      dot e (evalAx p (Array.addSmul x lam r)) =
        (evalAx p (Array.addSmul x lam r))[i]! := by
    exact dot_unitVector_left (evalAx p (Array.addSmul x lam r))
      m i (evalAx_size ..) hi
  have hX :
      dot e (evalAx p x) = (evalAx p x)[i]! := by
    exact dot_unitVector_left (evalAx p x) m i (evalAx_size ..) hi
  have hR :
      dot e (evalAx p r) = (evalAx p r)[i]! := by
    exact dot_unitVector_left (evalAx p r) m i (evalAx_size ..) hi
  rw [← hLeft, dot_y_evalAx_eq_dot_evalATy_x p e (Array.addSmul x lam r)
        heSize hySize]
  rw [dot_addSmul_right (evalATy p e) x r lam (by rw [evalATy_size, hx]) (by rw [hx, hr])]
  rw [← dot_y_evalAx_eq_dot_evalATy_x p e x heSize hx]
  rw [← dot_y_evalAx_eq_dot_evalATy_x p e r heSize hr]
  rw [hX, hR]

/-! ## `isStationary` Bool-to-Prop lemma.

  The executable check scans the fused `evalATySub` accumulator
  coordinatewise; `evalATySub_eq` rewrites it back to the
  `evalATy`/`arraySub` form that `StationarityAgainst` is stated
  against. -/
theorem isStationary_imp
    {m n : Nat} {p : Problem m n} {d : DualBundle m n}
    (h : isStationary p d = true) :
    StationarityAgainst p d p.c := by
  unfold isStationary at h
  rw [natAll_eq_true] at h
  intro j
  have hj := h j.val j.isLt
  rw [evalATySub_eq] at hj
  simpa using hj

/-- `(!o.isSome || decide P) = true ↔ (o = some _ → P)`. The Bool
    pattern used in `isRecessionRay` for the per-bound sign clauses. -/
private theorem or_not_isSome_decide_eq_true {α} {o : Option α} {P : Prop}
    [Decidable P] (h : (!o.isSome || decide P) = true) :
    o.isSome = true → P := by
  intro hSome
  rw [Bool.or_eq_true] at h
  rcases h with hNotSome | hP
  · simp [hSome] at hNotSome
  · exact of_decide_eq_true hP

/-- The `geLB` Bool check unpacked as a Prop: if `geLB x lo = true`
    then `lo = some l → l ≤ x`. -/
private theorem geLB_imp {x : Rat} {lo : Option Rat} (h : geLB x lo = true) :
    ∀ l, lo = some l → l ≤ x := by
  intro l hSome
  unfold geLB at h
  rw [hSome] at h
  exact of_decide_eq_true h

/-- The `leUB` Bool check unpacked as a Prop. -/
private theorem leUB_imp {x : Rat} {hi : Option Rat} (h : leUB x hi = true) :
    ∀ h', hi = some h' → x ≤ h' := by
  intro h' hSome
  unfold leUB at h
  rw [hSome] at h
  exact of_decide_eq_true h

theorem isPrimalFeasible_imp
    {m n : Nat} {p : Problem m n} {x : Vector Rat n}
    (h : isPrimalFeasible p x = true) :
    IsFeasible p x.toArray := by
  unfold isPrimalFeasible at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hCol, hRow⟩ := h
  have hxSize' : x.toArray.size = n := x.size_toArray
  rw [natAll_eq_true] at hCol hRow
  refine ⟨?_, ?_⟩
  · -- ColBoundsSatisfied
    refine ⟨hxSize', ?_⟩
    intro j
    have hj' := hCol j.val j.isLt
    simp only [Bool.and_eq_true] at hj'
    exact ⟨by simpa using geLB_imp hj'.1, by simpa using leUB_imp hj'.2⟩
  · -- RowBoundsSatisfied
    intro i
    have hi' := hRow i.val i.isLt
    simp only [Bool.and_eq_true] at hi'
    exact ⟨geLB_imp hi'.1, leUB_imp hi'.2⟩

theorem isRecessionRay_imp
    {m n : Nat} {p : Problem m n} {r : Vector Rat n}
    (h : isRecessionRay p r = true) :
    IsRecessionRay p r.toArray := by
  unfold isRecessionRay at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hCol, hRow⟩ := h
  rw [natAll_eq_true] at hCol hRow
  refine
    { size := r.size_toArray
      col_lo_nonneg := ?_
      col_hi_nonpos := ?_
      row_lo_nonneg := ?_
      row_hi_nonpos := ?_ }
  · intro j hLo
    have hj' := hCol j.val j.isLt
    simp only [Bool.and_eq_true] at hj'
    simpa using or_not_isSome_decide_eq_true hj'.1 hLo
  · intro j hHi
    have hj' := hCol j.val j.isLt
    simp only [Bool.and_eq_true] at hj'
    simpa using or_not_isSome_decide_eq_true hj'.2 hHi
  · intro i hLo
    have hi' := hRow i.val i.isLt
    simp only [Bool.and_eq_true] at hi'
    exact or_not_isSome_decide_eq_true hi'.1 hLo
  · intro i hHi
    have hi' := hRow i.val i.isLt
    simp only [Bool.and_eq_true] at hi'
    exact or_not_isSome_decide_eq_true hi'.2 hHi

/-- `isFarkasFeasible p d = true` implies the homogeneous componentwise
    stationarity `Aᵀ(yL − yU) + (zL − zU) = 0` plus the
    `DualNonnegZeroWhereAbsent` structure. Combined here so the
    soundness layer can consume `IsFarkasDualFeasible p d` in one
    step. -/
theorem isFarkasFeasible_imp
    {m n : Nat} {p : Problem m n} {d : DualBundle m n}
    (h : isFarkasFeasible p d = true) :
    IsFarkasDualFeasible p d := by
  unfold isFarkasFeasible at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hNonneg, hZero⟩ := h
  rw [natAll_eq_true] at hZero
  refine
    { nonneg_zero_absent := dualNonnegAndZeroWhereAbsent_imp hNonneg
      stationarity_zero := ?_ }
  intro j
  have hj := hZero j.val j.isLt
  rw [evalATySub_eq] at hj
  simpa using hj

end LP.Verify
