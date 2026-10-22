-- Draft/LaczFormalGraphCodes.lean -- D0 (part 4): from the real cyclic fan at a vertex to the CORNER CODES of `LaczFormalRegFan`.
-- For a congruent dissection with `idx i : Perm (Fin 3)` matching the angles of tile `i` to those of the model (types 0,1,2 = alpha,beta,gamma),
-- a corner of tile `i` at `V = pts k` whose sector is `(p, q)` gets the code `(t, u, w)` = (type at `V`, type of the tile vertex on the
-- clockwise ray `p`, type on the counterclockwise ray `q`) -- exactly the `RegFan` model.  `fan_codes_interior`: at an interior vertex all of
-- whose tiles have `V` as a vertex, the real fan is a cyclic list of such codes, with the ray adjacency, bijection with the tiles, and the
-- cyclic order realised by rays (`Par`).  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4: T_1..T_n, half-lines h_i; Lemma 4.5 proof).
import Erdos634.Draft.LaczFormalGraphSide
import Erdos634.Draft.LaczFormalRegFan
import Erdos634.Draft.LaczFormalCondE

open Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- Three distinct elements of `Fin 3` form a code: the RegFan code lookup returns the permutation back. -/
theorem code_spec (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    RegFan.tT (RegFan.code a b c) = a ∧ RegFan.tU (RegFan.code a b c) = b ∧ RegFan.tW (RegFan.code a b c) = c ∧
      RegFan.code a b c < 6 := by
  revert a b c; decide

/-- The code of a corner at `pts k` of a tile with type-permutation `σ`; `fl` records whether the sector `(p,q)` is the swapped
orientation `(vertex k+2, vertex k+1)`. -/
def codeOf (σ : Equiv.Perm (Fin 3)) (k : Fin 3) (fl : Bool) : ℕ :=
  if fl then RegFan.code (σ k) (σ (k + 2)) (σ (k + 1)) else RegFan.code (σ k) (σ (k + 1)) (σ (k + 2))

theorem codeOf_spec (σ : Equiv.Perm (Fin 3)) (k : Fin 3) (fl : Bool) :
    RegFan.tT (codeOf σ k fl) = σ k ∧
    RegFan.tU (codeOf σ k fl) = (if fl then σ (k + 2) else σ (k + 1)) ∧
    RegFan.tW (codeOf σ k fl) = (if fl then σ (k + 1) else σ (k + 2)) ∧ codeOf σ k fl < 6 := by
  have h1 : σ k ≠ σ (k + 1) := fun h => fin3_ne_one k (σ.injective h).symm
  have h2 : σ k ≠ σ (k + 2) := fun h => fin3_ne_two k (σ.injective h).symm
  have h3 : σ (k + 1) ≠ σ (k + 2) := fun h => fin3_add_ne k (σ.injective h)
  unfold codeOf
  cases fl
  · simp only [Bool.false_eq_true, if_false]
    exact code_spec _ _ _ h1 h2 h3
  · simp only [if_true]
    exact code_spec _ _ _ h2 h1 h3.symm

/-- **D0 interface, interior vertex whose tiles all have `V` as a vertex.**  -/
theorem fan_codes_interior (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (V : Plane)
    (hV : V ∈ interior D.target.carrier) (hvert : ∃ i k, (D.tile i).pts k = V)
    (hcorner : ∀ i, V ∈ (D.tile i).carrier → ∃ k, (D.tile i).pts k = V) :
    ∃ (p q : AtV D.toDissection V → V2) (e : ℕ → AtV D.toDissection V)
      (kk : AtV D.toDissection V → Fin 3) (fl : AtV D.toDissection V → Bool) (l : List ℕ),
      (∀ s, SecOK (p s) (q s)) ∧ (∀ s, wd (p s) (q s) = (D.tile s.1).localAngle V) ∧
      (∀ n, Par (p (e (n + 1))) (q (e n))) ∧
      (∀ n, e (n + Fintype.card (AtV D.toDissection V)) = e n) ∧
      Set.InjOn e (Set.Iio (Fintype.card (AtV D.toDissection V))) ∧
      (∀ s, ∃ j < Fintype.card (AtV D.toDissection V), e j = s) ∧
      (∀ s, (D.tile s.1).pts (kk s) = V ∧
        (p s, q s) = (if fl s then (toV2 ((D.tile s.1).pts (kk s + 2) - V), toV2 ((D.tile s.1).pts (kk s + 1) - V))
          else (toV2 ((D.tile s.1).pts (kk s + 1) - V), toV2 ((D.tile s.1).pts (kk s + 2) - V)))) ∧
      l.length = Fintype.card (AtV D.toDissection V) ∧
      (∀ n < Fintype.card (AtV D.toDissection V), l.getD n 0 = codeOf (idx (e n).1) (kk (e n)) (fl (e n))) := by
  classical
  obtain ⟨p, q, e, hok, hloc, hwd, hspec, hP, hcyc, hinj, hsurj⟩ := vertex_fan_interior D.toDissection V hV hvert
  have hex : ∀ s : AtV D.toDissection V, ∃ kf : Fin 3 × Bool, (D.tile s.1).pts kf.1 = V ∧
      (p s, q s) = (if kf.2 then (toV2 ((D.tile s.1).pts (kf.1 + 2) - V), toV2 ((D.tile s.1).pts (kf.1 + 1) - V))
        else (toV2 ((D.tile s.1).pts (kf.1 + 1) - V), toV2 ((D.tile s.1).pts (kf.1 + 2) - V))) := by
    intro s
    rcases hspec s with ⟨k, hk, hpq⟩ | ⟨hnv, -⟩
    · rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨(k, false), hk, by simp [h1, h2]⟩
      · exact ⟨(k, true), hk, by simp [h1, h2]⟩
    · obtain ⟨k, hk⟩ := hcorner s.1 s.2
      exact absurd hk (hnv k)
  choose kf hkf hpqf using hex
  refine ⟨p, q, e, fun s => (kf s).1, fun s => (kf s).2,
    (List.range (Fintype.card (AtV D.toDissection V))).map
      (fun n => if h : n < Fintype.card (AtV D.toDissection V) then
        codeOf (idx (e n).1) (kf (e n)).1 (kf (e n)).2 else 0), hok, hwd, hP, hcyc, hinj, hsurj,
    fun s => ⟨hkf s, hpqf s⟩, by simp, ?_⟩
  intro n hn
  simp [hn]

end Erdos634.Draft.LaczFormal.Graph
