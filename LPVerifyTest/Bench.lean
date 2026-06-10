/-
  Micro-benchmark for the compiled certificate-checker hot path
  (https://github.com/leanprover/lp-verify/issues/4).

  Constructs a size-`N` LP — diagonal sparse matrix, row bounds
  `(Ax)ᵢ ≥ 1`, column bounds `xⱼ ≥ 0`, objective `Σ xⱼ` — together
  with its exact optimality certificate, and times `checkOptimal`
  end to end.

  Two value profiles: integer data (denominator 1, so allocation is a
  larger share of the cost) and fractional data (denominator 3,
  exercising `Rat` gcd normalization). One synthetic profile, not a
  general claim: `Rat` arithmetic remains dominant in both.

  Run: `lake exe verify-bench [N] [iters]`.
-/
import LPVerify

open LP LP.Verify

namespace LPVerifyTest.Bench

/-- Diagonal LP `minimize Σ xⱼ s.t. (v·x)ᵢ ≥ 1, xⱼ ≥ 0` with optimum
    `x = 1/v`: row multipliers `1/v` witness optimality exactly. -/
def mkProblem (N : Nat) (v : Rat) : Problem N N :=
  { c := Vector.replicate N 1
    a := Array.ofFn (fun i : Fin N => (i, i, v))
    rowBounds := Vector.replicate N (some 1, none)
    colBounds := Vector.replicate N (some 0, none) }

def mkPrimal (N : Nat) (v : Rat) : Vector Rat N := Vector.replicate N (1/v)

def mkDual (N : Nat) (v : Rat) : DualBundle N N :=
  { rowLower := Vector.replicate N (1/v)
    rowUpper := Vector.replicate N 0
    colLower := Vector.replicate N 0
    colUpper := Vector.replicate N 0 }

def run (label : String) (N iters : Nat) (v : Rat) : IO Unit := do
  let p := mkProblem N v
  let x := mkPrimal N v
  let d := mkDual N v
  unless checkOptimal p x d do
    throw (IO.userError s!"bench ({label}): certificate unexpectedly rejected")
  let start ← IO.monoNanosNow
  let mut accepted := 0
  for _ in [0:iters] do
    if checkOptimal p x d then accepted := accepted + 1
  let stop ← IO.monoNanosNow
  let totalNs := stop - start
  IO.println s!"checkOptimal ({label}): N={N} iters={iters} accepted={accepted} \
    total={totalNs / 1000000}ms per-iter={totalNs / iters / 1000}µs"

def main (args : List String) : IO UInt32 := do
  let N := (args[0]?.bind (·.toNat?)).getD 2000
  let iters := max 1 ((args[1]?.bind (·.toNat?)).getD 50)
  run "integer data" N iters 1
  run "denominator 3" N iters 3
  return 0

end LPVerifyTest.Bench

def main (args : List String) : IO UInt32 := LPVerifyTest.Bench.main args
