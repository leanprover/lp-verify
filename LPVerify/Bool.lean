/-
  Boolean (decidable) certificate checkers.

  All `is*` and `check*` functions are total over well-typed `Problem`
  and certificate values.

  The per-coordinate loops are `Nat.fold` / `Nat.all` over indices
  (compiled to tail-recursive loops via their `@[csimp]` companions),
  so the hot path allocates no intermediate arrays of products and no
  boxed `Fin` index vectors.

  Soundness lemmas live in `LP.Verify.Sound`; they lift these
  `Bool` checks to the `Prop` predicates in `LP.Verify.Prop`.
-/
module

public import LPCore.Types

@[expose] public section

namespace LP.Verify

open LP

/-! ## Sparse matrix arithmetic.

  Stated via `Array.foldl`, which is what `Array.foldl_induction`
  operates on in `LP.Verify.Arith`.
-/

/-- Apply a single sparse entry `(r, c, v)` to the accumulator: add
    `v * x[c]!` into slot `r` of `out`. Both `out` and `x` keep their
    sizes; the `Fin` indices provide the shape facts. -/
@[inline] def applyAx {m n : Nat} (x : Array Rat) (out : Array Rat)
    (entry : Fin m × Fin n × Rat) : Array Rat :=
  let (r, c, v) := entry
  if h : r.val < out.size then
    out.set r.val (out[r.val]! + v * x[c.val]!) h
  else out

/-- Apply a single sparse entry `(r, c, v)` to the transposed
    accumulator: add `v * y[r]!` into slot `c` of `out`. -/
@[inline] def applyATy {m n : Nat} (y : Array Rat) (out : Array Rat)
    (entry : Fin m × Fin n × Rat) : Array Rat :=
  let (r, c, v) := entry
  if h : c.val < out.size then
    out.set c.val (out[c.val]! + v * y[r.val]!) h
  else out

/-- Apply a single sparse entry `(r, c, v)` to the transposed
    accumulator, reading the row multiplier as the difference
    `yL[r] − yU[r]`: fuses the row-multiplier subtraction into the
    scatter so `isStationary` / `isFarkasFeasible` never materialize
    `yL − yU`. -/
@[inline] def applyATySub {m n : Nat} (yL yU : Vector Rat m) (out : Array Rat)
    (entry : Fin m × Fin n × Rat) : Array Rat :=
  let (r, c, v) := entry
  if h : c.val < out.size then
    out.set c.val (out[c.val]! + v * (yL[r] - yU[r])) h
  else out

/-- Compute `Ax` as an `Array Rat` of length `m`. -/
def evalAx {m n : Nat} (p : Problem m n) (x : Array Rat) : Array Rat :=
  p.a.foldl (applyAx x) (Array.replicate m 0)

/-- Compute `Aᵀy` as an `Array Rat` of length `n`. -/
def evalATy {m n : Nat} (p : Problem m n) (y : Array Rat) : Array Rat :=
  p.a.foldl (applyATy y) (Array.replicate n 0)

/-- Compute `Aᵀ(yL − yU)` as an `Array Rat` of length `n` in one pass.
    Agrees with `evalATy` applied to the explicit difference vector —
    see `evalATySub_eq` in `LP.Verify.Arith`, which the soundness
    layer uses to keep its statements in `evalATy` form. -/
def evalATySub {m n : Nat} (p : Problem m n) (yL yU : Vector Rat m) :
    Array Rat :=
  p.a.foldl (applyATySub yL yU) (Array.replicate n 0)

/-! ### Output-size lemmas for `evalAx` / `evalATy`.

  Consumed by the soundness layer in `LP.Verify.Arith` /
  `LP.Verify.Sound`. -/

/-- `applyAx` preserves the output array's size. -/
theorem applyAx_size {m n : Nat} (x : Array Rat) (out : Array Rat)
    (entry : Fin m × Fin n × Rat) :
    (applyAx x out entry).size = out.size := by
  obtain ⟨r, c, v⟩ := entry
  show (if h : r.val < out.size
       then out.set r.val (out[r.val]! + v * x[c.val]!) h else out).size = out.size
  by_cases h : r.val < out.size
  · simp [h, Array.size_set]
  · simp [h]

/-- `applyATy` preserves the output array's size. -/
theorem applyATy_size {m n : Nat} (y : Array Rat) (out : Array Rat)
    (entry : Fin m × Fin n × Rat) :
    (applyATy y out entry).size = out.size := by
  obtain ⟨r, c, v⟩ := entry
  show (if h : c.val < out.size
       then out.set c.val (out[c.val]! + v * y[r.val]!) h else out).size = out.size
  by_cases h : c.val < out.size
  · simp [h, Array.size_set]
  · simp [h]

theorem evalAx_size {m n : Nat} (p : Problem m n) (x : Array Rat) :
    (evalAx p x).size = m := by
  unfold evalAx
  refine Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Array Rat) => acc.size = m) ?_ ?_
  · simp
  · intro i acc hAcc
    rw [applyAx_size]; exact hAcc

theorem evalATy_size {m n : Nat} (p : Problem m n) (y : Array Rat) :
    (evalATy p y).size = n := by
  unfold evalATy
  refine Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Array Rat) => acc.size = n) ?_ ?_
  · simp
  · intro i acc hAcc
    rw [applyATy_size]; exact hAcc

/-- Single-pass dot-product kernel: `Σ_{i < k} a[i]! * b[i]!`. The
    bound `k` is an explicit argument so `dot` (Array inputs, runtime
    size guard) and `vDot` (Vector inputs, length from the type) can
    share it. -/
def dotFold (a b : Array Rat) (k : Nat) : Rat :=
  Nat.fold k (fun i _ acc => acc + a[i]! * b[i]!) 0

/-- Dot product of two same-length `Array Rat`. Returns `0` on length
    mismatch (falls into the "false" branch of any caller). A single
    indexed fold — no intermediate array of products. The soundness
    layer connects it to its `dotPrefix` spec in `LP.Verify.Arith`. -/
def dot (a b : Array Rat) : Rat :=
  if a.size = b.size then dotFold a b a.size else 0

/-! ## Bound checks. -/

/-- `x ≥ lo` where `lo = none` is `−∞` (so the check is vacuous). -/
@[inline] def geLB (x : Rat) (lo : Option Rat) : Bool :=
  match lo with | none => true | some l => l ≤ x

/-- `x ≤ hi` where `hi = none` is `+∞` (so the check is vacuous). -/
@[inline] def leUB (x : Rat) (hi : Option Rat) : Bool :=
  match hi with | none => true | some h => x ≤ h

/-! ## Primal feasibility. -/

/-- Decide whether `x` is primal-feasible for the (normalized) `p`. -/
def isPrimalFeasible {m n : Nat} (p : Problem m n) (x : Vector Rat n) : Bool :=
  Nat.all n (fun j _hj =>
       let (lo, hi) := p.colBounds[j]
       geLB x[j] lo && leUB x[j] hi)
  && let ax := evalAx p x.toArray
     Nat.all m (fun i _hi =>
       let (lo, hi) := p.rowBounds[i]
       geLB ax[i]! lo && leUB ax[i]! hi)

/-! ## Dual feasibility. -/

/-- Each `DualBundle` vector matches the problem's dimensions in its
    type; here we additionally check that every entry is nonnegative,
    and any coordinate matching an absent bound is zero. -/
def dualNonnegAndZeroWhereAbsent {m n : Nat}
    (p : Problem m n) (d : DualBundle m n) : Bool :=
  Nat.all m (fun i _hi =>
       let (lo, hi) := p.rowBounds[i]
       decide (0 ≤ d.rowLower[i])
       && decide (0 ≤ d.rowUpper[i])
       && (!lo.isNone || decide (d.rowLower[i] = 0))
       && (!hi.isNone || decide (d.rowUpper[i] = 0)))
  && Nat.all n (fun j _hj =>
       let (lo, hi) := p.colBounds[j]
       decide (0 ≤ d.colLower[j])
       && decide (0 ≤ d.colUpper[j])
       && (!lo.isNone || decide (d.colLower[j] = 0))
       && (!hi.isNone || decide (d.colUpper[j] = 0)))

/-- Componentwise subtraction of two same-length `Array Rat`. Returns
    `#[]` on length mismatch. Only the soundness layer consumes this
    (`StationarityAgainst` in `LP.Verify.Prop`); the executable
    checkers fuse the subtraction via `evalATySub` instead.
    Implemented via `Array.zipWith` so the soundness layer can use
    `getElem_zipWith` directly. -/
def arraySub (a b : Array Rat) : Array Rat :=
  if a.size = b.size then Array.zipWith (· - ·) a b else #[]

/-- Vector-typed dot product. Same as `dot` but the type rules out the
    length-mismatch case, so there is no `if a.size = b.size` guard
    and no zero-on-mismatch fallback. -/
@[inline] def vDot {n : Nat} (a b : Vector Rat n) : Rat :=
  dotFold a.toArray b.toArray n

/-- Stationarity check: `Aᵀ(yL − yU) + (zL − zU) = c`. The matrix term
    comes from the one-pass `evalATySub`; the column difference and
    the comparison against `p.c` are fused into a single coordinate
    scan, so no dense temporaries are built. -/
def isStationary {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Bool :=
  let aty := evalATySub p d.rowLower d.rowUpper
  Nat.all n (fun j _hj =>
    aty[j]! + (d.colLower[j] - d.colUpper[j]) == p.c[j])

/-- Dual feasibility for the optimality certificate. -/
def isDualFeasible {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Bool :=
  dualNonnegAndZeroWhereAbsent p d && isStationary p d

/-- Farkas (homogeneous) dual feasibility: same shape as
    `isStationary`, but with stationarity `Aᵀ(yL − yU) + (zL − zU) = 0`
    instead of `= c`. -/
def isFarkasFeasible {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Bool :=
  dualNonnegAndZeroWhereAbsent p d
  && let aty := evalATySub p d.rowLower d.rowUpper
     Nat.all n (fun j _hj =>
       aty[j]! + (d.colLower[j] - d.colUpper[j]) == 0)

/-! ## Objective values. -/

/-- Primal objective `c · x + objOffset`. Returns `objOffset` on
    length mismatch. The soundness layer states optimality against
    arbitrary `Array Rat` points, so this stays Array-typed; the
    executable checkers use `vPrimalObj`. -/
def primalObj {m n : Nat} (p : Problem m n) (x : Array Rat) : Rat :=
  dot p.c.toArray x + p.objOffset

/-- Primal objective with the length in the type: same value as
    `primalObj` on the underlying array (`vPrimalObj_eq_primalObj` in
    `LP.Verify.Arith`), without the runtime size guard. -/
@[inline] def vPrimalObj {m n : Nat} (p : Problem m n) (x : Vector Rat n) : Rat :=
  vDot p.c x + p.objOffset

/-- Contribution of a single optional lower bound: `mult * lo` or `0`. -/
@[inline] def loContrib (lo : Option Rat) (mult : Rat) : Rat :=
  lo.elim 0 (mult * ·)

/-- Contribution of a single optional upper bound: `mult * hi` or `0`. -/
@[inline] def hiContrib (hi : Option Rat) (mult : Rat) : Rat :=
  hi.elim 0 (mult * ·)

/-- The bound combination underlying `dualObj` and `boundCombinationPos`:
    `Σᵢ (yLᵢ · rₗᵢ − yUᵢ · rᵤᵢ) + Σⱼ (zLⱼ · cₗⱼ − zUⱼ · cᵤⱼ)`.
    The `+ objOffset` for `dualObj` and the strict-positive check for
    `boundCombinationPos` are layered on top. The `Nat.fold` sums are
    bridged to the soundness layer's `Array.range` folds by
    `natFold_eq_range_foldl` in `LP.Verify.Arith`. -/
def dualBoundCombination {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Rat :=
  let rowPart := Nat.fold m (fun i _ (acc : Rat) =>
    let (lo, hi) := p.rowBounds[i]!
    acc + loContrib lo d.rowLower[i]! - hiContrib hi d.rowUpper[i]!) 0
  let colPart := Nat.fold n (fun j _ (acc : Rat) =>
    let (lo, hi) := p.colBounds[j]!
    acc + loContrib lo d.colLower[j]! - hiContrib hi d.colUpper[j]!) 0
  rowPart + colPart

/-- Dual objective in the canonical lower/upper split form:

      Σᵢ (yLᵢ · rₗᵢ − yUᵢ · rᵤᵢ)
    + Σⱼ (zLⱼ · cₗⱼ − zUⱼ · cᵤⱼ)
    + objOffset

    A coordinate contributes zero whenever the matching bound is `none`
    (regardless of the multiplier — see `dualNonnegAndZeroWhereAbsent`).

    `checkOptimal` always requires `isDualFeasible` to hold before
    consulting this value. -/
def dualObj {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Rat :=
  dualBoundCombination p d + p.objOffset

/-- The Farkas strict-positivity step: the bound combination must be
    strictly positive (with the same convention as `dualObj`, but
    without the `objOffset`). -/
def boundCombinationPos {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Bool :=
  decide (0 < dualBoundCombination p d)

/-! ## Top-level checks for each certificate kind. -/

/-- Optimal certificate: primal feasibility, dual feasibility, and
    strong duality `c·x* + objOffset = dualObj`. -/
def checkOptimal {m n : Nat}
    (p : Problem m n) (x : Vector Rat n) (d : DualBundle m n) : Bool :=
  isPrimalFeasible p x
  && isDualFeasible p d
  && vPrimalObj p x == dualObj p d

/-- Infeasibility (Farkas) certificate: homogeneous dual feasibility
    plus strict-positive bound combination. -/
def checkInfeasible {m n : Nat} (p : Problem m n) (d : DualBundle m n) : Bool :=
  isFarkasFeasible p d
  && boundCombinationPos p d

/-- Recession-cone check for an unbounded ray. Each row / column with
    a finite bound on a given side produces the corresponding sign
    constraint on the corresponding `(Ar)ᵢ` / `rⱼ`. Equality rows /
    boxed columns collapse to `= 0`. -/
def isRecessionRay {m n : Nat} (p : Problem m n) (r : Vector Rat n) : Bool :=
  Nat.all n (fun j _hj =>
       let (lo, hi) := p.colBounds[j]
       (!lo.isSome || decide (0 ≤ r[j]))
       && (!hi.isSome || decide (r[j] ≤ 0)))
  && let ar := evalAx p r.toArray
     Nat.all m (fun i _hi =>
       let (lo, hi) := p.rowBounds[i]
       (!lo.isSome || decide (0 ≤ ar[i]!))
       && (!hi.isSome || decide (ar[i]! ≤ 0)))

/-- Unbounded certificate: a feasible base point and an improving
    recession ray. -/
def checkUnbounded {m n : Nat} (p : Problem m n) (x ray : Vector Rat n) : Bool :=
  isPrimalFeasible p x
  && isRecessionRay p ray
  && vDot p.c ray < 0

end LP.Verify
