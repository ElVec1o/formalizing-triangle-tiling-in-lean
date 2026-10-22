-- Draft/LaczFormalR2Ex.lean -- R(a) = R0(a) at the EXCEPTIONAL denominators n = 6, 8, 10, 12, 18, 24, 30, 60 for every primitive triple EXCEPT the 27 listed ones
-- (all six orderings excluded): the certificate `allCertEx n excl` of `CaseACorF.allCert` with the excluded triples skipped.  UNAUDITED.
-- Credit: Laczkovich (1995, Lemma S); our `CaseACorF`.
import Erdos634.Draft.CaseACorF

open scoped BigOperators Classical
open Erdos634.LemmaS

namespace Erdos634.Draft.LaczFormal

def allCertEx (n : ℕ) (excl : List (ℕ × ℕ × ℕ)) : Bool :=
  (List.range n).all fun a0 => (List.range n).all fun a1 =>
    if 1 ≤ a0 ∧ 1 ≤ a1 ∧ a0 + a1 < n ∧ Nat.gcd a0 (Nat.gcd a1 (n - a0 - a1)) = 1 ∧
        excl.contains (a0, a1, n - a0 - a1) = false then
      cert n a0 a1 (n - a0 - a1) else true

theorem of_allCertEx {n : ℕ} {excl : List (ℕ × ℕ × ℕ)} (hA : allCertEx n excl = true) (a : Fin 3 → ℕ)
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hex : excl.contains (a 0, a 1, a 2) = false) : relSpace n a = trivSpace n a := by
  rw [Fin.sum_univ_three] at hsum
  have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
  have hn : 0 < n := by omega
  have ha2 : a 2 = n - a 0 - a 1 := by omega
  unfold allCertEx at hA
  simp only [List.all_eq_true, List.mem_range] at hA
  have hc := hA (a 0) (by omega) (a 1) (by omega)
  rw [← ha2, if_pos ⟨h0, h1, by omega, hgcd, hex⟩] at hc
  exact le_antisymm (fun e he => cert_sound hn hc he) (trivSpace_le n a)

def excl_6 : List (ℕ × ℕ × ℕ) := [(1, 1, 4), (1, 4, 1), (4, 1, 1), (1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), (3, 2, 1)]
set_option maxHeartbeats 16000000 in
theorem allCertEx_6 : allCertEx 6 excl_6 = true := by
  unfold excl_6
  decide +kernel

def excl_8 : List (ℕ × ℕ × ℕ) := [(1, 2, 5), (1, 5, 2), (2, 1, 5), (2, 5, 1), (5, 1, 2), (5, 2, 1)]
set_option maxHeartbeats 16000000 in
theorem allCertEx_8 : allCertEx 8 excl_8 = true := by
  unfold excl_8
  decide +kernel

def excl_10 : List (ℕ × ℕ × ℕ) := [(1, 2, 7), (1, 7, 2), (2, 1, 7), (2, 7, 1), (7, 1, 2), (7, 2, 1), (1, 3, 6), (1, 6, 3), (3, 1, 6), (3, 6, 1), (6, 1, 3), (6, 3, 1)]
set_option maxHeartbeats 16000000 in
theorem allCertEx_10 : allCertEx 10 excl_10 = true := by
  unfold excl_10
  decide +kernel

def excl_12 : List (ℕ × ℕ × ℕ) := [(1, 2, 9), (1, 9, 2), (2, 1, 9), (2, 9, 1), (9, 1, 2), (9, 2, 1), (1, 3, 8), (1, 8, 3), (3, 1, 8), (3, 8, 1), (8, 1, 3), (8, 3, 1), (1, 4, 7), (1, 7, 4), (4, 1, 7), (4, 7, 1), (7, 1, 4), (7, 4, 1), (2, 3, 7), (2, 7, 3), (3, 2, 7), (3, 7, 2), (7, 2, 3), (7, 3, 2), (3, 4, 5), (3, 5, 4), (4, 3, 5), (4, 5, 3), (5, 3, 4), (5, 4, 3)]
set_option maxHeartbeats 16000000 in
theorem allCertEx_12 : allCertEx 12 excl_12 = true := by
  unfold excl_12
  decide +kernel

def excl_18 : List (ℕ × ℕ × ℕ) := [(1, 3, 14), (1, 14, 3), (3, 1, 14), (3, 14, 1), (14, 1, 3), (14, 3, 1), (2, 3, 13), (2, 13, 3), (3, 2, 13), (3, 13, 2), (13, 2, 3), (13, 3, 2), (3, 7, 8), (3, 8, 7), (7, 3, 8), (7, 8, 3), (8, 3, 7), (8, 7, 3)]
set_option maxHeartbeats 16000000 in
theorem allCertEx_18 : allCertEx 18 excl_18 = true := by
  unfold excl_18
  decide +kernel

def excl_24 : List (ℕ × ℕ × ℕ) := [(1, 4, 19), (1, 19, 4), (4, 1, 19), (4, 19, 1), (19, 1, 4), (19, 4, 1), (1, 6, 17), (1, 17, 6), (6, 1, 17), (6, 17, 1), (17, 1, 6), (17, 6, 1), (4, 7, 13), (4, 13, 7), (7, 4, 13), (7, 13, 4), (13, 4, 7), (13, 7, 4), (5, 6, 13), (5, 13, 6), (6, 5, 13), (6, 13, 5), (13, 5, 6), (13, 6, 5)]
set_option maxHeartbeats 16000000 in
theorem allCertEx_24 : allCertEx 24 excl_24 = true := by
  unfold excl_24
  decide +kernel

def excl_30 : List (ℕ × ℕ × ℕ) := [(1, 5, 24), (1, 24, 5), (5, 1, 24), (5, 24, 1), (24, 1, 5), (24, 5, 1), (1, 10, 19), (1, 19, 10), (10, 1, 19), (10, 19, 1), (19, 1, 10), (19, 10, 1), (5, 6, 19), (5, 19, 6), (6, 5, 19), (6, 19, 5), (19, 5, 6), (19, 6, 5), (5, 7, 18), (5, 18, 7), (7, 5, 18), (7, 18, 5), (18, 5, 7), (18, 7, 5), (5, 12, 13), (5, 13, 12), (12, 5, 13), (12, 13, 5), (13, 5, 12), (13, 12, 5), (7, 10, 13), (7, 13, 10), (10, 7, 13), (10, 13, 7), (13, 7, 10), (13, 10, 7)]
set_option maxHeartbeats 16000000 in
theorem allCertEx_30 : allCertEx 30 excl_30 = true := by
  unfold excl_30
  decide +kernel

def excl_60 : List (ℕ × ℕ × ℕ) := [(1, 10, 49), (1, 49, 10), (10, 1, 49), (10, 49, 1), (49, 1, 10), (49, 10, 1), (7, 10, 43), (7, 43, 10), (10, 7, 43), (10, 43, 7), (43, 7, 10), (43, 10, 7), (10, 13, 37), (10, 37, 13), (13, 10, 37), (13, 37, 10), (37, 10, 13), (37, 13, 10), (10, 19, 31), (10, 31, 19), (19, 10, 31), (19, 31, 10), (31, 10, 19), (31, 19, 10)]
set_option maxHeartbeats 16000000 in
theorem allCertEx_60 : allCertEx 60 excl_60 = true := by
  unfold excl_60
  decide +kernel
def excl_3 : List (ℕ × ℕ × ℕ) := [(1, 1, 1)]
def excl_4 : List (ℕ × ℕ × ℕ) := [(1, 1, 2), (1, 2, 1), (2, 1, 1)]

end Erdos634.Draft.LaczFormal
