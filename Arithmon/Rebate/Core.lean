/-
  Arithmon / Rebate -- the in-framework-theorem complexity rebate (generic)
  ========================================================================

  Q5 of the Sieve methodology paper. The generic, framework-independent layer:
  the rebate definitions and a minimal worked example. The faithful frozen
  grammar and its certified counts live in `Arithmon.Sieve.GStruct`; the
  per-client R1 audit (is a given GIFT relation a theorem?) will depend on
  GIFT core (see the repository README, two-layer architecture).

  THE ARGUMENT. A standalone coincidence "constant ~ formula" is found by
  SEARCH over an expression space E(G, k). Its surprise is bounded by how much
  of that space matches the target as well or better: the search pays a
  look-elsewhere factor equal to the value-haystack it scanned (|V(G, k)|, or
  the rank at the match tolerance). A relation that is a THEOREM of a
  pre-specified formal structure is not chosen by search: the formula is forced
  by the axioms and committed before the target is consulted. Its trials factor
  is 1. The rebate is the log of the ratio. It is the binary indicator of two
  externally witnessable facts (R1: it is a theorem; R2: it was pre-committed)
  times the certified haystack term, so it is not a continuous fitting resource
  a richer alphabet can buy. That is why it escapes the closeness/coverage
  (N2) trap by construction.

  "Theorem" here means built and certified (a proven consequence of the
  framework axioms), NOT intuitionistically constructive: GIFT's Lean is
  classical. The kinship to the constructivist lineage is in spirit.

  Pure Lean 4 core (no Mathlib).
-/

namespace Arithmon.Rebate

/-! ## The rebate, as quantities over a (certified) value-haystack -/

/-- The search account's look-elsewhere factor at an exact match: the number
    of distinct reachable values (the haystack actually scanned). In the real
    grammar this is `Arithmon.Sieve.GStruct.count k`, machine-checked. -/
def searchFactor (haystack : Nat) : Nat := haystack

/-- The theorem account's trials factor: 1, conditional on R1 (is a theorem)
    and R2 (pre-committed). -/
def theoremFactor : Nat := 1

/-- The rebate in haystack units: the whole look-elsewhere term, awarded iff
    R1 and R2 both hold. As a ratio `searchFactor / theoremFactor`; the paper
    reports its log10. -/
def rebateRatio (haystack : Nat) (R1 R2 : Bool) : Nat :=
  if R1 && R2 then searchFactor haystack / theoremFactor else 1

/-! ## Minimal worked example (toy grammar)

A self-contained illustration over atoms {1, 2, 3} and ops {+, *, /}. The real
frozen grammar is in `Arithmon.Sieve.GStruct`; this is only the smallest thing
that exhibits the search-versus-theorem contrast end to end. -/

inductive Op | add | mul | div
deriving DecidableEq, Repr

inductive Expr
  | atom : Rat → Expr
  | bin  : Op → Expr → Expr → Expr
deriving Repr

def Expr.nodes : Expr → Nat
  | .atom _ => 1
  | .bin _ a b => 1 + a.nodes + b.nodes

def applyOp : Op → Rat → Rat → Rat
  | .add, x, y => x + y
  | .mul, x, y => x * y
  | .div, x, y => x / y

def Expr.eval : Expr → Rat
  | .atom q => q
  | .bin o a b => applyOp o a.eval b.eval

def atoms : List Rat := [1, 2, 3]
def ops : List Op := [Op.add, Op.mul, Op.div]

def table (k : Nat) : Array (List Expr) := Id.run do
  let mut t : Array (List Expr) := #[[]]
  for s in [1:k+1] do
    if s == 1 then
      t := t.push (atoms.map Expr.atom)
    else
      let mut acc : List Expr := []
      for i in [1:s] do
        let j := s - 1 - i
        if j ≥ 1 then
          for o in ops do
            for l in t[i]! do
              for r in t[j]! do
                acc := (Expr.bin o l r) :: acc
      t := t.push acc
  return t

def upTo (k : Nat) : List Expr :=
  let t := table k
  (List.range k).flatMap (fun i => t[i+1]!)

def nub {α} [BEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def evalsUpTo (k : Nat) : List Rat := (upTo k).map Expr.eval
def numExprs (k : Nat) : Nat := (upTo k).length
/-- Value-haystack size of the toy grammar (the toy search factor). -/
def numDistinct (k : Nat) : Nat := (nub (evalsUpTo k)).length
def reachable (k : Nat) (t : Rat) : Bool := (evalsUpTo k).contains t

theorem toy_haystack_k5 : numExprs 5 = 516 := by native_decide
/-- The toy search look-elsewhere factor at budget 5: 36 distinct values. -/
theorem toy_values_k5 : numDistinct 5 = 36 := by native_decide
theorem toy_koide_reachable : reachable 5 (2/3) = true := by native_decide

/-- The pre-committed witness: a single fixed expression written before the
    target is consulted. Its evaluation to 2/3 is a THEOREM, so its trials
    factor is 1 against the search account's haystack. -/
def koideWitness : Expr := Expr.bin Op.div (Expr.atom 2) (Expr.atom 3)

theorem koideWitness_eval  : koideWitness.eval = 2/3 := by native_decide
theorem koideWitness_nodes : koideWitness.nodes = 3 := by decide

/-- The contrast, made explicit: with the witness a theorem (R1) and
    pre-committed (R2), the rebate awards the full haystack term; absent either,
    it collapses to 1. Both numbers are machine-checked. -/
example : rebateRatio (numDistinct 5) true true = 36 := by native_decide
example : rebateRatio (numDistinct 5) true false = 1 := by native_decide

end Arithmon.Rebate
