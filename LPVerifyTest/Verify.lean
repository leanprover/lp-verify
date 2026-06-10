/-
  Behavioral tests for the certificate checker: hand-constructed
  fixtures driven through `verifyOutcome`, covering each `Verified`
  constructor on the accept side and tampered / incomplete / over-
  budget certificates on the reject side.

  Run via `lake test` (the `verify-tests` executable).
-/

import LPVerify

open LP LP.Verify

namespace LPVerifyTest.Verify

private def assertM (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)

private def mkSol {m n : Nat} (status : SolveStatus)
    (primal : Option (Vector Rat n) := none)
    (dual : Option (DualBundle m n) := none)
    (ray : Option (Vector Rat n) := none) : Solution m n :=
  { status, objective := none, certificate := { primal, dual, ray }, log := "" }

/-! ### Optimal: minimize x subject to x ≥ 1 (no rows).

  Optimum x = 1. Dual: reduced cost 1 on the column lower bound. -/

def optP : Problem 0 1 :=
  { c := #v[1], a := #[], rowBounds := #v[], colBounds := #v[(some 1, none)] }

def optDual : DualBundle 0 1 :=
  { rowLower := #v[], rowUpper := #v[], colLower := #v[1], colUpper := #v[0] }

def case_optimalAccepted : IO Unit := do
  match verifyOutcome {} none optP (mkSol .optimal (primal := some #v[1]) (dual := some optDual)) with
  | .optimal x _ => assertM (x == #v[1]) "optimal: wrong witness"
  | _ => throw (IO.userError "optimal: valid certificate not accepted")

/-- Tampered primal: x = 2 is feasible but no longer matches the dual
    objective, so strong duality fails and the result is unchecked. -/
def case_optimalTamperedRejected : IO Unit := do
  match verifyOutcome {} none optP (mkSol .optimal (primal := some #v[2]) (dual := some optDual)) with
  | .unchecked .optimal => pure ()
  | _ => throw (IO.userError "optimal: tampered certificate not rejected")

/-- Missing dual: terminal status without its certificate field. -/
def case_optimalMissingDual : IO Unit := do
  match verifyOutcome {} none optP (mkSol .optimal (primal := some #v[1])) with
  | .unchecked .optimal => pure ()
  | _ => throw (IO.userError "optimal: missing dual not rejected")

/-! ### Infeasible: row x ≥ 1 against column bound x ≤ 0.

  Farkas: multiplier 1 on the row lower bound, 1 on the column upper
  bound; the combination certifies 0 ≥ 1. -/

def infP : Problem 1 1 :=
  { c := #v[0], a := #[(0, 0, 1)]
    rowBounds := #v[(some 1, none)], colBounds := #v[(none, some 0)] }

def infDual : DualBundle 1 1 :=
  { rowLower := #v[1], rowUpper := #v[0], colLower := #v[0], colUpper := #v[1] }

def case_infeasibleAccepted : IO Unit := do
  match verifyOutcome {} none infP (mkSol .infeasible (dual := some infDual)) with
  | .infeasible _ => pure ()
  | _ => throw (IO.userError "infeasible: valid Farkas certificate not accepted")

/-- Tampered Farkas: zero row multiplier breaks the strict positivity. -/
def case_infeasibleTamperedRejected : IO Unit := do
  let bad : DualBundle 1 1 :=
    { rowLower := #v[0], rowUpper := #v[0], colLower := #v[0], colUpper := #v[0] }
  match verifyOutcome {} none infP (mkSol .infeasible (dual := some bad)) with
  | .unchecked .infeasible => pure ()
  | _ => throw (IO.userError "infeasible: tampered certificate not rejected")

/-! ### Unbounded: minimize −x subject to x ≥ 0 (no rows).

  Base point x = 0, improving ray r = 1. -/

def unbP : Problem 0 1 :=
  { c := #v[-1], a := #[], rowBounds := #v[], colBounds := #v[(some 0, none)] }

def case_unboundedAccepted : IO Unit := do
  match verifyOutcome {} none unbP
      (mkSol .unbounded (primal := some #v[0]) (ray := some #v[1])) with
  | .unbounded x r _ =>
      assertM (x == #v[0] && r == #v[1]) "unbounded: wrong witnesses"
  | _ => throw (IO.userError "unbounded: valid certificate not accepted")

/-- Missing ray: the base point alone certifies nothing. -/
def case_unboundedMissingRay : IO Unit := do
  match verifyOutcome {} none unbP (mkSol .unbounded (primal := some #v[0])) with
  | .unchecked .unbounded => pure ()
  | _ => throw (IO.userError "unbounded: missing ray not rejected")

/-- Non-improving ray: r = 1 with c = 1 has c·r > 0. -/
def case_unboundedBadRay : IO Unit := do
  let p : Problem 0 1 :=
    { c := #v[1], a := #[], rowBounds := #v[], colBounds := #v[(some 0, none)] }
  match verifyOutcome {} none p
      (mkSol .unbounded (primal := some #v[0]) (ray := some #v[1])) with
  | .unchecked .unbounded => pure ()
  | _ => throw (IO.userError "unbounded: non-improving ray not rejected")

/-! ### Budget and pass-through statuses. -/

/-- A zero bit-length budget rejects any certificate carrying a 1. -/
def case_budgetExceeded : IO Unit := do
  match verifyOutcome {} (some 0) optP
      (mkSol .optimal (primal := some #v[1]) (dual := some optDual)) with
  | .unchecked .budgetExceeded => pure ()
  | _ => throw (IO.userError "budget: over-budget certificate not rejected")

/-- Non-terminal solver statuses pass through unchecked. -/
def case_passthrough : IO Unit := do
  match verifyOutcome {} none optP (mkSol .timeLimit) with
  | .unchecked .timeLimit => pure ()
  | _ => throw (IO.userError "passthrough: timeLimit not preserved")

/-! ### Maximize canonicalization: maximize x subject to x ≤ 4.

  Optimum x = 4; the checker canonicalizes to minimize −x. The dual
  puts reduced cost 1 on the column *upper* bound: stationarity for
  the canonicalized objective is −1 = zL − zU with zU = 1. -/

def maxP : Problem 0 1 :=
  { c := #v[1], a := #[], rowBounds := #v[], colBounds := #v[(none, some 4)] }

def maxDual : DualBundle 0 1 :=
  { rowLower := #v[], rowUpper := #v[], colLower := #v[0], colUpper := #v[1] }

def case_maximizeAccepted : IO Unit := do
  match verifyOutcome { sense := .maximize } none maxP
      (mkSol .optimal (primal := some #v[4]) (dual := some maxDual)) with
  | .optimal x _ => assertM (x == #v[4]) "maximize: wrong witness"
  | _ => throw (IO.userError "maximize: valid certificate not accepted")

def main : IO UInt32 := do
  case_optimalAccepted
  case_optimalTamperedRejected
  case_optimalMissingDual
  case_infeasibleAccepted
  case_infeasibleTamperedRejected
  case_unboundedAccepted
  case_unboundedMissingRay
  case_unboundedBadRay
  case_budgetExceeded
  case_passthrough
  case_maximizeAccepted
  IO.println "lp-verify certificate tests: all passed"
  return 0

end LPVerifyTest.Verify

def main : IO UInt32 := LPVerifyTest.Verify.main
