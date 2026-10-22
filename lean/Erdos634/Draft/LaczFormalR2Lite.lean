-- Draft/LaczFormalR2Lite.lean -- LIGHT copy of the pure-arithmetic certificate functions of `CaseACorF` (sawZ, det3, unitsL, minor2, minor3, cert) with NO Mathlib import,
-- so that a `decide +kernel` chunk of `allCertR` runs in a small process (the Mathlib import alone is ~5 GB of resident memory).  Equality with the `CaseACorF` definitions
-- is proved by `rfl` in `LaczFormalR2Bridge`.  UNAUDITED.  Credit: Laczkovich (1995, Lemma S); our CaseACorF.
namespace Erdos634.Lite

def sawZ (n m : Nat) : Int := if m % n == 0 then 0 else 2 * ((m % n : Nat) : Int) - n

def det3 (p0 q0 r0 p1 q1 r1 p2 q2 r2 : Int) : Int :=
  p0 * (q1 * r2 - r1 * q2) - q0 * (p1 * r2 - r1 * p2) + r0 * (p1 * q2 - q1 * p2)

def unitsL (n : Nat) : List Nat := (List.range n).filter (fun k => Nat.gcd k n == 1)

def minor2 (n a b : Nat) : Bool :=
  (unitsL n).any fun k => (unitsL n).any fun k' =>
    sawZ n (k * a) * sawZ n (k' * b) - sawZ n (k' * a) * sawZ n (k * b) != 0

def minor3 (n a b c : Nat) : Bool :=
  (unitsL n).any fun k => (unitsL n).any fun k' => (unitsL n).any fun k'' =>
    det3 (sawZ n (k * a)) (sawZ n (k * b)) (sawZ n (k * c))
      (sawZ n (k' * a)) (sawZ n (k' * b)) (sawZ n (k' * c))
      (sawZ n (k'' * a)) (sawZ n (k'' * b)) (sawZ n (k'' * c)) != 0

def cert (n a0 a1 a2 : Nat) : Bool :=
  if a0 = a1 then minor2 n a0 a2 else if a1 = a2 then minor2 n a0 a1
  else if a0 = a2 then minor2 n a0 a1 else if 2 * a0 = n then minor2 n a1 a2
  else if 2 * a1 = n then minor2 n a0 a2 else if 2 * a2 = n then minor2 n a0 a1
  else minor3 n a0 a1 a2

def allCertR (n lo len : Nat) : Bool :=
  (List.range' lo len).all fun a0 => (List.range n).all fun a1 =>
    if 1 ≤ a0 ∧ 1 ≤ a1 ∧ a0 + a1 < n ∧ Nat.gcd a0 (Nat.gcd a1 (n - a0 - a1)) = 1 then
      cert n a0 a1 (n - a0 - a1) else true

end Erdos634.Lite
