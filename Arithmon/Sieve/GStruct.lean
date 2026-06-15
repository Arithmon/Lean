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
  Sieve engine: |E_rat| = 32, 91, 1416, 9782, 105329 at budgets 1 to 5. The
  budget-5 count enumerates ~4 million raw values before deduplication, which an
  O(n log n) sort-dedup (not the earlier O(n^2) filter) makes tractable for
  `native_decide`. Pure Lean 4 core.
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

/-- Sort then drop adjacent duplicates: O(n log n) deduplication by exact `Rat`
    equality (core Lean has no `List.dedup`; `Array.qsort` and a linear scan
    replace the earlier O(n^2) membership filter, which is what lets the counts
    reach budget 5, where the raw value stream is ~4 million entries). -/
def sortDedup (a : Array Rat) : Array Rat := Id.run do
  let s := a.qsort (fun x y => x < y)
  let mut out : Array Rat := #[]
  let mut prev : Option Rat := none
  for x in s do
    if prev != some x then out := out.push x
    prev := some x
  return out

/-- Dynamic program over node count, mirroring the engine: `L[n]` holds the
    distinct values reachable by an expression of EXACTLY `n` nodes, sorted and
    deduplicated. -/
def levels (k : Nat) : Array (Array Rat) := Id.run do
  let mut L : Array (Array Rat) := #[#[]]
  for n in [1:k+1] do
    if n == 1 then
      L := L.push (sortDedup ((atoms.filter okMag).toArray))
    else
      let mut raw : Array Rat := #[]
      for v in L[n-1]! do
        for uo in [0,1] do
          match unOp uo v with
          | some r => if okMag r then raw := raw.push r
          | none => pure ()
      for i in [1:n-1] do
        let j := n-1-i
        for a in L[i]! do
          for b in L[j]! do
            for bo in [0,1,2,3,4] do
              match binOp bo a b with
              | some r => if okMag r then raw := raw.push r
              | none => pure ()
      L := L.push (sortDedup raw)
  return L

/-- All distinct values reachable within `k` nodes. -/
def valuesUpTo (k : Nat) : Array Rat :=
  let L := levels k
  sortDedup ((List.range k).foldl (fun acc i => acc ++ L[i+1]!) #[])

/-- |E(G_STRUCT, k)| after value canonicalization: the trials-factor
    denominator. -/
def count (k : Nat) : Nat := (valuesUpTo k).size

/-- A target value is reachable within `k` nodes (the haystack contains it). -/
def reachable (k : Nat) (t : Rat) : Bool := (valuesUpTo k).contains t

/-- The EXACT isolation rank within a rational window `[lo, hi]` at budget `k`:
    the number of distinct grammar values that fall in the window, i.e. that
    match a measurement at least as well as a claim sitting at the window edge
    (the scorecard `D18` statistic, exactly). `Rat` equality is the dedup key, so
    this is free of the float engine's 12-digit merge/split risk for the
    rational fragment it covers. The window edge must be the EXACT claim value
    (not `measured - dev_float`), else the claim can fall a float-epsilon outside
    its own window; with an exact edge the claim is always counted, so a
    budget-unique match certifies as rank 1. The GIFT-specific windows (a
    measured value plus or minus its achieved deviation) and the resulting ranks
    are the methodology paper's payload; this is the generic, certifiable
    statistic. -/
def isolationRank (k : Nat) (lo hi : Rat) : Nat :=
  ((valuesUpTo k).filter (fun v => lo ≤ v && v ≤ hi)).size

/-- Illustration on a TOY window, no framework input: at budget 1 the only
    distinct values in `[1, 2]` are the leaf atoms 1 and 2, so the rank is 2.
    Demonstrates the statistic computes and is machine-checkable. -/
theorem isolationRank_toy : isolationRank 1 1 2 = 2 := by native_decide

/-- A window can be empty of competitors save a single value: the toy window
    `[81/52, 81/52]` (a degenerate point) at budget 5 contains exactly the one
    value `81/52`, certifying the machinery returns 1 on a unique-in-window
    point. (A real measured window is wider; its rank is the paper's payload.) -/
theorem isolationRank_point : isolationRank 5 (81/52) (81/52) = 1 := by
  native_decide

/- ------------------------------------------------------------------------
   Certified counts (rational fragment), budgets 1 to 5. Each matches the
   exact-rational Python re-run of the Sieve engine. These are the
   machine-checked trials-factor denominators (figure F2 data).
   ------------------------------------------------------------------------ -/

theorem alphabet_size : atoms.length = 32 := by native_decide
theorem count_k1 : count 1 = 32 := by native_decide
theorem count_k2 : count 2 = 91 := by native_decide
theorem count_k3 : count 3 = 1416 := by native_decide
theorem count_k4 : count 4 = 9782 := by native_decide
/-- The search look-elsewhere factor at budget 5: 105329 distinct values. -/
theorem count_k5 : count 5 = 105329 := by native_decide

/- ------------------------------------------------------------------------
   The two N0/N1 survivors, reachable in the real frozen grammar (not a toy).
   ------------------------------------------------------------------------ -/

/-- Koide's 2/3 is reachable by search in the frozen G_STRUCT at budget 3,
    e.g. as (atom 2) / (atom 3). A SEARCH for it pays the certified factor
    `count 3 = 1416`; a pre-committed theorem witness would pay 1
    (see `Arithmon.Rebate.Core`). -/
theorem koide_reachable : reachable 3 (2/3) = true := by native_decide

/-- The m_H/m_W value 81/52 is reachable by search at budget 5, e.g. as
    (3 + 78)/52. The gross look-elsewhere factor at that budget is
    `count 5 = 105329`; the budget-filtered isolation rank against a measured
    window is computed by `isolationRank` above (the GIFT-specific window and its
    rank are the methodology paper's payload, kept out of this public layer). -/
theorem mHmW_reachable : reachable 5 (81/52) = true := by native_decide

end Arithmon.Sieve.GStruct
