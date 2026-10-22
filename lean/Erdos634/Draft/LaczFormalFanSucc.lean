import Erdos634.Draft.LaczFormalGraphExt

/-!
# The successor sector in a vertex fan (reusable form)

Erdős #634, band program, rule W2 (`PROOF_W2.md`).  Credit: AI assistant (item 3, band program), Laczkovich (DCG 48
(2012), Sect. 4: the fan of angular domains at a vertex), Beeson–Roșu, Beeson, Paliy.  UNAUDITED.

For any vertex `V` of any dissection and its uniform fan `F : ExtFan D V κ` (tiles through `V` plus the virtual
exterior sectors), put `F.P o`, `F.Q o` for the start and end ray of the sector `o : AtV D V ⊕ κ`.

* `succ_exists`   every sector has a successor `o'` with `Par (P o') (Q o)` (the next sector in the cyclic order);
* `succ_unique`   the successor is unique (two sectors starting along the same ray coincide);
* `pred_unique`   dually, the predecessor is unique;
* `succ_eq_of_step`  a tile that has a side leaving `V` along `d` with the tile on the left of `d` starts its sector
  along `d`; so if some sector ends along `d`, that tile IS its successor;
* `arms_of_cross` the rays of a tile sector at a vertex of the tile are its two edge vectors, in the order given by
  the sign of the cross product.
-/

namespace Erdos634.Draft.LaczFormal.Graph

open Erdos634.Geometry

variable {N : ℕ}

namespace ExtFan

variable {D : Dissection N} {V : Plane} {κ : Type} [Fintype κ]

/-- Start ray of the sector `o` of the full family (tiles through `V` and virtual sectors). -/
def P (F : ExtFan D V κ) : AtV D V ⊕ κ → V2 := Sum.elim F.p F.pe
/-- End ray of the sector `o`. -/
def Q (F : ExtFan D V κ) : AtV D V ⊕ κ → V2 := Sum.elim F.q F.qe

@[simp] theorem P_inl (F : ExtFan D V κ) (s : AtV D V) : F.P (Sum.inl s) = F.p s := rfl
@[simp] theorem Q_inl (F : ExtFan D V κ) (s : AtV D V) : F.Q (Sum.inl s) = F.q s := rfl
@[simp] theorem P_inr (F : ExtFan D V κ) (j : κ) : F.P (Sum.inr j) = F.pe j := rfl
@[simp] theorem Q_inr (F : ExtFan D V κ) (j : κ) : F.Q (Sum.inr j) = F.qe j := rfl

theorem ok (F : ExtFan D V κ) (o : AtV D V ⊕ κ) : SecOK (F.P o) (F.Q o) := by
  rcases o with s | j
  · exact F.hok s
  · exact F.hokE j

/-- Every sector has a successor. -/
theorem succ_exists (F : ExtFan D V κ) (o : AtV D V ⊕ κ) : ∃ o', Par (F.P o') (F.Q o) := by
  obtain ⟨j, -, hj⟩ := F.hsurj o
  exact ⟨F.e (j + 1), by rw [← hj]; exact F.hP j⟩

/-- Two distinct sectors do not start along the same ray. -/
theorem start_ne (F : ExtFan D V κ) {o1 o2 : AtV D V ⊕ κ} (h : o1 ≠ o2) : ¬ Par (F.P o2) (F.P o1) :=
  start_inj F.P F.Q F.ok (fun s t hst z => F.disj_all hst z) h

/-- Two distinct sectors do not end along the same ray. -/
theorem end_ne (F : ExtFan D V κ) {o1 o2 : AtV D V ⊕ κ} (h : o1 ≠ o2) : ¬ Par (F.Q o2) (F.Q o1) :=
  end_inj' F.P F.Q F.ok (fun s t hst z => F.disj_all hst z) h

/-- **Successor, uniqueness.** -/
theorem succ_unique (F : ExtFan D V κ) {o o1 o2 : AtV D V ⊕ κ} (h1 : Par (F.P o1) (F.Q o))
    (h2 : Par (F.P o2) (F.Q o)) : o1 = o2 := by
  by_contra hne
  exact F.start_ne hne (h2.trans h1.symm)

/-- **Predecessor, uniqueness.** -/
theorem pred_unique (F : ExtFan D V κ) {o o1 o2 : AtV D V ⊕ κ} (h1 : Par (F.P o) (F.Q o1))
    (h2 : Par (F.P o) (F.Q o2)) : o1 = o2 := by
  by_contra hne
  exact F.end_ne hne (h2.symm.trans h1)

/-- A sector is never its own successor. -/
theorem succ_ne_self (F : ExtFan D V κ) (o : AtV D V ⊕ κ) : ¬ Par (F.P o) (F.Q o) :=
  fun h => par_not_secok (F.ok o) h.symm

/-- A tile with a side leaving `V` along `d`, on the left of `d`, starts its sector along `d`. -/
theorem step_start (F : ExtFan D V κ) {d : V2} {i : Fin N} {U' : Plane} (hS : TriStep (D.tile i) d V U')
    (hi : V ∈ (D.tile i).carrier) : Par (F.p ⟨i, hi⟩) d := by
  obtain ⟨kk, f, g, hk, -⟩ := id hS
  obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data (F.hspec ⟨i, hi⟩) ⟨kk, hk⟩
  exact triStep_start hS kk' fl hk' hp hq (F.hok _)

/-- A tile with a side arriving at `V` along `d`, on the left of `d`, ends its sector along `-d`. -/
theorem step_end (F : ExtFan D V κ) {d : V2} {i : Fin N} {U : Plane} (hS : TriStep (D.tile i) d U V)
    (hi : V ∈ (D.tile i).carrier) : Par (F.q ⟨i, hi⟩) (-d.1, -d.2) := by
  obtain ⟨kk, f, g, hk, hf, -⟩ := id hS
  obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data (F.hspec ⟨i, hi⟩) ⟨f, hf⟩
  exact triStep_end hS kk' fl hk' hp hq (F.hok _)

/-- **The successor of a sector ending along `d` is the tile with a left side leaving `V` along `d`.** -/
theorem succ_of_step (F : ExtFan D V κ) {o : AtV D V ⊕ κ} {d : V2} (hQ : Par (F.Q o) d) {i : Fin N} {U' : Plane}
    (hS : TriStep (D.tile i) d V U') (hi : V ∈ (D.tile i).carrier) {o' : AtV D V ⊕ κ}
    (ho' : Par (F.P o') (F.Q o)) : o' = Sum.inl ⟨i, hi⟩ :=
  F.succ_unique ho' (by rw [P_inl]; exact (F.step_start hS hi).trans hQ.symm)

end ExtFan

end Erdos634.Draft.LaczFormal.Graph
