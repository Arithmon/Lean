/-
  Arithmon / Sieve -- the frozen G_STRUCT grammar, exactly certified
  ==================================================================

  A faithful Lean port of the frozen G_STRUCT(betti = 21, 77) grammar of the
  Sieve (freeze/GRAMMARS_FREEZE.md v1.0, DOI 10.5281/zenodo.20666879), and
  machine-checked counts of its expression space, the denominator of every
  trials-factor computation (skeleton figure F2 / section 7.3).

  WHY LEAN ADDS SOMETHING HERE. The Python engine dedups by VALUE using a
  float rounded to 12 significant digits. That is a practical proxy with a
  (tiny) risk of false merges or splits. This module certifies the EXACT count
  of the RATIONAL FRAGMENT: the grammar restricted to operations that keep
  values rational (no sqrt, no transcendentals), with `Rat` equality as the
  dedup key. The result is a provably correct count, strictly stronger
  epistemically than the float proxy, for the fragment it covers. The full
  grammar (with sqrt) stays in Python; this is the auditable rational core.

  Faithful to the freeze on: the alphabet (32 distinct leaf values from the
  50 named leaves: dims + ranks of compact simple Lie groups of rank <= 8,
  Betti numbers 21 and 77, integers 1..9), the operations (+, -, *, /, ^ and
  the unary inv, sq), and the guards (integer exponents in [-4, 4], no 0^0,
  no 0^negative, division by nonzero, magnitude in (1e-12, 1e12)). Excluded:
  sqrt (irrational), hence "rational fragment".

  Cross-checked against an exact-rational (`fractions.Fraction`) re-run of the
  Sieve engine: |E_rat| = 32, 91, 1416 at budgets 1, 2, 3. Pure Lean 4 core.
-/

namespace Arithmon.Sieve.GStruct

/-- The 32 distinct leaf VALUES of the frozen G_STRUCT(betti = 21, 77) alphabet.
    Provenance: integers 1..9; Lie dims (A1..A8 = 3,8,15,24,35,48,63,80;
    B2..B8 = 10,21,36,55,78,105,136; C3..C8 share B's dims; D4..D8 =
    28,45,66,91,120; G2=14, F4=52, E6=78, E7=133, E8=248); Betti 21 (= a Lie
    dim already) and 77 (the only Betti not otherwise present). The 50 named
    leaves collapse to these 32 values; expression counts are value-based. -/
def atoms : List Rat :=
  [1,2,3,4,5,6,7,8,9,10,14,15,21,24,28,35,36,45,48,52,55,63,66,77,78,80,91,
   105,120,133,136,248]

def magHi : Rat := 1000000000000
def magLo : Rat := 1 / 1000000000000
def ratAbs (v : Rat) : Rat := if v < 0 then -v else v
/-- Magnitude guard, mirroring the engine's `_ok`. -/
def okMag (v : Rat) : Bool := magLo < ratAbs v && ratAbs v < magHi

def ratPowNat : Rat → Nat → Rat
  | _, 0 => 1
  | a, (n+1) => a * ratPowNat a n
def ratPowInt (a : Rat) : Int → Rat
  | Int.ofNat k => ratPowNat a k
  | Int.negSucc k => 1 / ratPowNat a (k+1)

/-- `^` with the frozen guards: integer exponent in [-4,4], no 0^0,
    no 0^negative. -/
def powOp (a b : Rat) : Option Rat :=
  if b.den != 1 then none
  else
    let n := b.num
    if n < -4 || n > 4 then none
    else if n == 0 then (if a == 0 then none else some 1)
    else if a == 0 && n < 0 then none
    else some (ratPowInt a n)

/-- Binary ops 0:+ 1:- 2:* 3:/ 4:^ (division guarded). -/
def binOp (op : Nat) (a b : Rat) : Option Rat :=
  match op with
  | 0 => some (a+b) | 1 => some (a-b) | 2 => some (a*b)
  | 3 => if b == 0 then none else some (a/b)
  | _ => powOp a b

/-- Unary ops 0:inv (guarded) 1:sq. sqrt is excluded (rational fragment). -/
def unOp (op : Nat) (v : Rat) : Option Rat :=
  match op with
  | 0 => if v == 0 then none else some (1/v)
  | _ => some (v*v)

/-- Order-insensitive deduplication by exact `Rat` equality (no `List.dedup`
    in core Lean). -/
def nub (l : List Rat) : List Rat :=
  l.foldl (fun acc x => if acc.contains x then acc else x :: acc) []

/-- Dynamic program over node count, mirroring the engine: `L[n]` holds the
    distinct values reachable by an expression of EXACTLY `n` nodes. -/
def levels (k : Nat) : Array (List Rat) := Id.run do
  let mut L : Array (List Rat) := #[[]]
  for n in [1:k+1] do
    if n == 1 then
      L := L.push (nub (atoms.filter okMag))
    else
      let mut raw : List Rat := []
      for v in L[n-1]! do
        for uo in [0,1] do
          match unOp uo v with
          | some r => if okMag r then raw := r :: raw
          | none => pure ()
      for i in [1:n-1] do
        let j := n-1-i
        for a in L[i]! do
          for b in L[j]! do
            for bo in [0,1,2,3,4] do
              match binOp bo a b with
              | some r => if okMag r then raw := r :: raw
              | none => pure ()
      L := L.push (nub raw)
  return L

/-- All distinct values reachable within `k` nodes. -/
def valuesUpTo (k : Nat) : List Rat :=
  nub ((List.range k).flatMap (fun i => (levels k)[i+1]!))

/-- |E(G_STRUCT, k)| after value canonicalization: the trials-factor
    denominator. -/
def count (k : Nat) : Nat := (valuesUpTo k).length

/-- A target value is reachable within `k` nodes (the haystack contains it). -/
def reachable (k : Nat) (t : Rat) : Bool := (valuesUpTo k).contains t

/- ------------------------------------------------------------------------
   Certified counts (rational fragment). Match the exact-rational Python
   re-run. These are the machine-checked trials-factor denominators.
   ------------------------------------------------------------------------ -/

theorem alphabet_size : atoms.length = 32 := by native_decide
theorem count_k1 : count 1 = 32 := by native_decide
theorem count_k2 : count 2 = 91 := by native_decide
/-- The search look-elsewhere factor at budget 3: 1416 distinct values. -/
theorem count_k3 : count 3 = 1416 := by native_decide

/- ------------------------------------------------------------------------
   The Koide value in the real frozen grammar (not a toy).
   ------------------------------------------------------------------------ -/

/-- Koide's 2/3 is reachable by search in the frozen G_STRUCT at budget 3,
    e.g. as (atom 2) / (atom 3). A SEARCH for it pays the certified factor
    `count 3 = 1416`; a pre-committed theorem witness would pay 1
    (see `Arithmon.Rebate.Core`). -/
theorem koide_reachable : reachable 3 (2/3) = true := by native_decide

end Arithmon.Sieve.GStruct
