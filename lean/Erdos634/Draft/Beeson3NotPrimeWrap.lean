import Erdos634.Beeson3NotPrime

/-!
# Beeson3NotPrime — Beeson Thm 3 arithmetic exclusions: wrapper

Key results:
- `triquadratic_not_prime`: prime N with K ∣ N and N + M² = 2K² → False
- `fourcomp_not_prime`: (2f²−e²)(3f²−e²)k² is not prime
- `prime_mul_sq_ne`: prime N with N ∤ D → N·D ≠ M²
- `isobeta_square_not_prime`: iso-β square tiling equation is not prime

VERIFIED: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.Beeson3NotPrimeWrap

open Erdos634.Beeson3

theorem b3_triquadratic_not_prime (N K M : ℕ) (hN : N.Prime) (hodd : Odd N)
    (hK : K ∣ N) (heq : N + M ^ 2 = 2 * K ^ 2) : False :=
  triquadratic_not_prime N K M hN hodd hK heq

theorem b3_fourcomp_not_prime (e f k : ℕ) (he : 1 ≤ e) (hef : e < f) (hk : 1 ≤ k) :
    ¬ ((2 * f ^ 2 - e ^ 2) * ((3 * f ^ 2 - e ^ 2) * k ^ 2)).Prime :=
  fourcomp_not_prime e f k he hef hk

theorem b3_prime_mul_sq_ne (N D M A : ℕ) (hN : N.Prime) (hND : ¬ N ∣ D) (hA : 0 < A) :
    N * A ^ 2 ≠ M ^ 2 * D :=
  prime_mul_sq_ne N D hN hND M A hA

theorem b3_isobeta_square_not_prime (N e f M Y D K : ℕ) (hN : N.Prime) (hodd : Odd N)
    (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hD : e ^ 2 + D = 3 * f ^ 2) (hK : e ^ 2 + K = f ^ 2)
    (heq : N * (e + f) ^ 2 = M ^ 2 * D) (hsq : N * K = Y ^ 2) : False :=
  isobeta_square_not_prime N e f M Y D K hN hodd he hef hcop hD hK heq hsq

-- Non-vacuity: fourcomp_not_prime with e=1, f=2, k=1
example : ¬ ((2 * 2 ^ 2 - 1 ^ 2) * ((3 * 2 ^ 2 - 1 ^ 2) * 1 ^ 2)).Prime :=
  b3_fourcomp_not_prime 1 2 1 (by norm_num) (by norm_num) (by norm_num)

#print axioms b3_triquadratic_not_prime
#print axioms b3_fourcomp_not_prime

end Erdos634.Draft.Beeson3NotPrimeWrap
