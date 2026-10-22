-- Draft/LaczFormalRGChain.lean -- S4 of PLAN_THM21: the chain core of the half-fan lemma without the line condition: a chain of corner tiles `c 1, .., c n` at a vertex `V`
-- (consecutive tiles share a ray, inner rays are starts of maximal segments).  Either an edge of `Gamma_a` starts at `V`, or the arm of `c 1` and the arm of `c n` on the two outer rays
-- are both `a` / both not `a` exactly when the number of non-`alpha` corners is even.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemmas 4.2, 4.5, 9.1 proofs), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGHalf

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- Parity core without the boundary condition. -/
theorem parity_core2 (n : ℕ) (hn : 1 ≤ n) (P Q f : ℕ → Bool)
    (htile : ∀ m, 1 ≤ m → m ≤ n → ((f m = false → P m = false ∧ Q m = false) ∧ (f m = true → P m ≠ Q m))) :
    (∃ m, 1 ≤ m ∧ m < n ∧ Q m ≠ P (m + 1)) ∨
      (Q n = P 1 ↔ (∑ j ∈ Finset.Icc 1 n, (if f j = true then 1 else 0)) % 2 = 0) := by
  by_cases hcon : ∃ m, 1 ≤ m ∧ m < n ∧ Q m ≠ P (m + 1)
  · exact Or.inl hcon
  right
  have hcon' : ∀ m, 1 ≤ m → m < n → Q m = P (m + 1) := by
    intro m h1 h2
    by_contra h
    exact hcon ⟨m, h1, h2, h⟩
  have key : ∀ m, 1 ≤ m → m ≤ n → (Q m = P 1 ↔ (∑ j ∈ Finset.Icc 1 m, (if f j = true then 1 else 0)) % 2 = 0) := by
    intro m hm1 hmn
    induction m, hm1 using Nat.le_induction with
    | base =>
      have h1 := htile 1 le_rfl hn
      rw [Finset.Icc_self, Finset.sum_singleton]
      generalize hx : P 1 = x at *
      generalize hy : Q 1 = y at *
      cases hf : f 1
      · obtain ⟨h2, h3⟩ := h1.1 hf
        rw [h2, h3]; simp
      · have h2 := h1.2 hf
        cases x <;> cases y <;> simp_all
    | succ m hm ih =>
      have ih' := ih (by omega)
      have hnext := hcon' m hm (by omega)
      have h1 := htile (m + 1) (by omega) hmn
      rw [Finset.sum_Icc_succ_top (by omega)]
      generalize hx : P 1 = x at *
      generalize hq : Q m = q at *
      generalize hq' : Q (m + 1) = q' at *
      generalize hp : P (m + 1) = p' at *
      cases hf : f (m + 1)
      · obtain ⟨h2, h3⟩ := h1.1 hf
        rw [h3]
        rw [hnext, h2] at ih'
        simpa using ih'
      · have h2 := h1.2 hf
        subst hnext
        cases q <;> cases q' <;> cases x <;> simp_all <;> omega
  exact key n hn le_rfl

set_option maxHeartbeats 1600000 in
/-- **Chain core.**  See the file header. -/
theorem chain_core (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection V κ) (n : ℕ) (hn : 1 ≤ n)
    (c : ℕ → AtV D.toRegionDissection V)
    (hcpos : ∀ l, 1 ≤ l → l ≤ n → 0 < crs (F.p (c l)) (F.q (c l)))
    (hadj : ∀ l, 1 ≤ l → l < n → Par (F.p (c (l + 1))) (F.q (c l)))
    (hnb : ∀ l, 1 ≤ l → l < n → NoBack D.toRegionDissection (F.q (c l)) V) :
    (∃ H', GaEdge D.toRegionDissection (slen D 0) V H') ∨
      ((nsq (F.p (c 1)) = slen D 0 ^ 2 ↔ nsq (F.q (c n)) = slen D 0 ^ 2) ↔
        (∑ l ∈ Finset.Icc 1 n, (if ∃ k : Fin 3, (D.tile (c l).1).pts k = V ∧ idx (c l).1 k ≠ 0 then 1 else 0)) % 2 = 0) := by
  classical
  have hcd : ∀ m, 1 ≤ m → m ≤ n → ∃ (kk : Fin 3) (fl : Bool), (D.tile (c m).1).pts kk = V ∧
      F.p (c m) = toV2 ((D.tile (c m).1).pts (armP kk fl) - V) ∧ F.q (c m) = toV2 ((D.tile (c m).1).pts (armQ kk fl) - V) :=
    fun m h1 h2 => spec_corner_data (F.hspec (c m)) (corner_vertex F (c m) (hcpos m h1 h2))
  let P : ℕ → Bool := fun m => decide (nsq (F.p (c m)) = slen D 0 ^ 2)
  let Q : ℕ → Bool := fun m => decide (nsq (F.q (c m)) = slen D 0 ^ 2)
  let f : ℕ → Bool := fun m => decide (∃ k, (D.tile (c m).1).pts k = V ∧ idx (c m).1 k ≠ 0)
  have htile : ∀ m, 1 ≤ m → m ≤ n → ((f m = false → P m = false ∧ Q m = false) ∧ (f m = true → P m ≠ Q m)) := by
    intro m h1 h2
    obtain ⟨kk, fl, hk, hp, hq⟩ := hcd m h1 h2
    have hb := corner_bits D idx hidx hab hac fl hk hp hq
    have hf : (∃ k, (D.tile (c m).1).pts k = V ∧ idx (c m).1 k ≠ 0) ↔ idx (c m).1 kk ≠ 0 := by
      constructor
      · rintro ⟨k, hk', hne'⟩
        have : k = kk := (D.tile (c m).1).indep.injective (hk'.trans hk.symm)
        rw [← this]; exact hne'
      · intro h; exact ⟨kk, hk, h⟩
    constructor
    · intro hfm
      have hfm' : ¬ (∃ k, (D.tile (c m).1).pts k = V ∧ idx (c m).1 k ≠ 0) := by simpa [f] using hfm
      have h0 : idx (c m).1 kk = 0 := by
        by_contra hh; exact hfm' (hf.mpr hh)
      have := hb.1 h0
      simp [P, Q, this.1, this.2]
    · intro hfm
      have hfm' : ∃ k, (D.tile (c m).1).pts k = V ∧ idx (c m).1 k ≠ 0 := by simpa [f] using hfm
      have h0 := hf.mp hfm'
      have := hb.2 h0
      simp only [P, Q, ne_eq, decide_eq_decide]
      tauto
  rcases parity_core2 n hn P Q f htile with ⟨m, hm1, hm2, hmne⟩ | hpar
  · left
    have hcx := hcpos m hm1 (by omega)
    have hcy := hcpos (m + 1) (by omega) (by omega)
    refine ga_edge_of_ray D idx hidx hnc F (c m) (c (m + 1)) hcx hcy (hadj m hm1 hm2) (hnb m hm1 hm2) ?_
    simp only [P, Q, ne_eq, decide_eq_decide] at hmne
    by_cases h1 : nsq (F.q (c m)) = slen D 0 ^ 2
    · left
      refine ⟨h1, fun h2 => hmne ⟨fun _ => h2, fun _ => h1⟩⟩
    · right
      refine ⟨h1, ?_⟩
      by_contra h2
      exact hmne ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  · right
    simp only [P, Q, decide_eq_decide] at hpar
    have hsum : (∑ l ∈ Finset.Icc 1 n, (if f l = true then 1 else 0)) =
        (∑ l ∈ Finset.Icc 1 n, (if ∃ k : Fin 3, (D.tile (c l).1).pts k = V ∧ idx (c l).1 k ≠ 0 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro l _
      simp only [f, decide_eq_true_eq]
    rw [← hsum]
    constructor
    · intro h; exact hpar.mp (by simpa using h.symm)
    · intro h; simpa using (hpar.mpr h).symm

end Erdos634.Draft.LaczFormal.RG
