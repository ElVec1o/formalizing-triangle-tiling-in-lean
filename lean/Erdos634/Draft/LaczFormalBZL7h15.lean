-- Draft/LaczFormalBZL7h15.lean -- Beeson (arXiv 1206.1974v7) Lemma 10.3 + Lemma 10.4 (centre part) (G1): EVERY centre starts an outgoing GaEdge of the a-type / b-type side.
--   Proof (printed Lemma 10.3 = parity of the five a-edges and three b-edges, `centre_ab_or_ac_bc` of BZL7f1) on the REAL fan: the cyclic fan of five corner sectors (`centre_fan`), labels from `cd`/`arm_lens`,
--   `NoBack` from `centre_no_opp` (no two rays opposite), and Laczkovich's `ga_edge_of_ray` for the relabelled tile.
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Lemmas 10.3, 10.4), Laczkovich (DCG 48 (2012), Sect. 4, 8.1), Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h14

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem sigma_other (σ : Equiv.Perm (Fin 3)) (u : Fin 3) (hu : u ≠ σ 0) : u = σ 1 ∨ u = σ 2 := by
  have h := (σ.apply_symm_apply u).symm
  have h0 : σ.symm u ≠ 0 := fun h' => hu (by rw [← h', σ.apply_symm_apply])
  generalize σ.symm u = w at *
  fin_cases w
  · exact absurd rfl h0
  · left; simpa using h
  · right; simpa using h

theorem nat_pred_mod (m i : ℕ) (hi : i < m) : ((i + 1) % m + m - 1) % m = i := by
  rcases Nat.lt_or_ge (i + 1) m with h | h
  · rw [Nat.mod_eq_of_lt h]
    have : i + 1 + m - 1 = i + m := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have h' : i + 1 = m := by omega
    rw [h', Nat.mod_self]
    have : 0 + m - 1 = i := by omega
    rw [this, Nat.mod_eq_of_lt hi]

/-- **G1.**  A centre starts an outgoing `GaEdge` of side `slen D (sigma 0)` (`sigma 0 = 0` or `1`), under `NotComb`. -/
theorem g1_of_centre (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (σ : Equiv.Perm (Fin 3)) (hσ : σ 0 = 0 ∨ σ 0 = 1)
    (hnc : NotComb (slen D (σ 0)) (slen D (σ 1)) (slen D (σ 2)))
    {X : Plane} (hX : ∃ i k, (D.tile i).pts k = X)
    (hc0 : cnt D idx X 0 = 0) (hc1 : cnt D idx X 1 = 2) (hc2 : cnt D idx X 2 = 3) :
    ∃ H, GaEdge D.toRegionDissection (slen D (σ 0)) X H := by
  classical
  obtain ⟨F, hcor, hcard⟩ := centre_fan D P hreg idx hidxA hβ hγ hX hc0 hc1 hc2
  haveI hemp : IsEmpty Empty := inferInstance
  set m := Fintype.card (AtV D.toRegionDissection X) with hm
  have hmpos : 0 < m := card_pos_atV F hemp
  haveI : NeZero m := ⟨hmpos.ne'⟩
  let s : Fin m → AtV D.toRegionDissection X := fun i => tl F hemp i.val
  have hs_inj : Function.Injective s := by
    intro i j h; apply Fin.ext; exact tl_inj F hemp i.isLt j.isLt h
  have hs_surj : Function.Surjective s := by
    intro x; obtain ⟨j, hj, hjx⟩ := tl_surj F hemp x; exact ⟨⟨j, hj⟩, hjx⟩
  let ty : Fin m → Fin 3 := fun i => idx (s i).1 (cd D F hcor (s i)).1
  let l : Fin m → Fin 3 := fun i => idx (s i).1 (armQ (cd D F hcor (s i)).1 (cd D F hcor (s i)).2)
  let r : Fin m → Fin 3 := fun i => idx (s i).1 (armP (cd D F hcor (s i)).1 (cd D F hcor (s i)).2)
  have hl : ∀ i, l i ≠ ty i := fun i h => armQ_ne _ _ ((idx _).injective h)
  have hr : ∀ i, r i ≠ ty i := fun i h => armP_ne _ _ ((idx _).injective h)
  have hlr : ∀ i, l i ≠ r i := fun i h => armPQ_ne _ _ ((idx _).injective h).symm
  have hcount : ∀ j : Fin 3, (Finset.univ.filter (fun i : Fin m => ty i = j)).card = cnt D idx X j := by
    intro j
    rw [cnt_atv D idx (fun x => (cd D F hcor x).1) (fun x => (cd_spec D F hcor x).1) j]
    refine Finset.card_bij (fun i _ => s i) ?_ ?_ ?_
    · intro i hi; simpa [ty] using hi
    · intro i _ i' _ h; exact hs_inj h
    · intro x hx
      obtain ⟨i, hi⟩ := hs_surj x
      refine ⟨i, ?_, hi⟩
      subst hi
      simpa [ty] using hx
  have hcen := centre_ab_or_ac_bc ty l r hl hr hlr (by rw [hcount, hc0]) (by rw [hcount, hc1]) (by rw [hcount, hc2])
  have hray : ∃ i : Fin m, r i ≠ l (i + 1) ∧ (r i = σ 0 ∨ l (i + 1) = σ 0) := by
    have pick : ∀ (i : Fin m) (a b : Fin 3), a ≠ b → (σ 0 = a ∨ σ 0 = b) → ((r i = a ∧ l (i + 1) = b) ∨ (r i = b ∧ l (i + 1) = a)) →
        r i ≠ l (i + 1) ∧ (r i = σ 0 ∨ l (i + 1) = σ 0) := by
      intro i a b hab hta hi
      rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hta with h | h
      · exact ⟨by rw [h1, h2]; exact hab, Or.inl (by rw [h1, h])⟩
      · exact ⟨by rw [h1, h2]; exact hab, Or.inr (by rw [h2, h])⟩
      · exact ⟨by rw [h1, h2]; exact hab.symm, Or.inr (by rw [h2, h])⟩
      · exact ⟨by rw [h1, h2]; exact hab.symm, Or.inl (by rw [h1, h])⟩
    rcases hcen with ⟨i, hi⟩ | ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    · exact ⟨i, pick i 0 1 (by decide) (by rcases hσ with h | h <;> simp [h]) hi⟩
    · rcases hσ with h | h
      · exact ⟨i, pick i 0 2 (by decide) (Or.inl h) hi⟩
      · exact ⟨j, pick j 1 2 (by decide) (Or.inl h) hj⟩
  obtain ⟨i, hne, hone⟩ := hray
  have hne_sig : ∀ u : Fin 3, u ≠ σ 0 → slen D u ≠ slen D (σ 0) := by
    intro u hu
    rcases sigma_other σ u hu with h | h
    · rw [h]; exact (notComb_ne01 hnc).symm
    · rw [h]; exact (notComb_ne02 hnc).symm
  have hsq : ∀ u : Fin 3, u ≠ σ 0 → slen D u ^ 2 ≠ slen D (σ 0) ^ 2 := by
    intro u hu h
    have := (pow_left_inj₀ (slen_pos D u).le (slen_pos D (σ 0)).le two_ne_zero).mp h
    exact hne_sig u hu this
  -- the two adjacent sectors
  have hval : ∀ i : Fin m, (i + 1 : Fin m).val = (i.val + 1) % m := by
    intro i
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m)]
  set x := s i with hx
  set y := s (i + 1) with hy
  have hyl : y = tl F hemp (i.val + 1) := by
    show tl F hemp (i + 1 : Fin m).val = _
    rw [hval, ← tl_mod F hemp]
  have hxy : Par (F.p y) (F.q x) := by rw [hyl]; exact tl_adj F hemp i.val
  have hq : nsq (F.q x) = slen D (r i) ^ 2 := by
    obtain ⟨hk, -, hq⟩ := cd_spec D F hcor x
    have := (arm_lens D idx hidx x.1 (cd D F hcor x).1 (cd D F hcor x).2).2
    rw [hk] at this
    rw [hq]; exact this
  have hp : nsq (F.p y) = slen D (l (i + 1)) ^ 2 := by
    obtain ⟨hk, hp, -⟩ := cd_spec D F hcor y
    have := (arm_lens D idx hidx y.1 (cd D F hcor y).1 (cd D F hcor y).2).1
    rw [hk] at this
    rw [hp]; exact this
  -- NoBack
  have hnone1 : ∀ s' : AtV D.toRegionDissection X, ¬ Par (F.p s') (neg2 (F.q x)) := by
    intro s' hP
    have hi' : (i.val + 1) % m < m := Nat.mod_lt _ hmpos
    have e : tl F hemp (0 + ((i.val + 1) % m + m - 1) % m) = x := by
      rw [nat_pred_mod m i.val i.isLt, zero_add]
    exact centre_no_opp D idx hidxA hβ hγ hα F hcor hemp hc0 hc1 hc2 0 ((i.val + 1) % m) hi' s'
      (by rw [e]; exact hP)
  have hnb : NoBack D.toRegionDissection (F.q x) X := by
    apply ExtFan.noBack_of_none F
    intro s'
    refine ⟨hnone1 s', ?_⟩
    intro hQ
    obtain ⟨j, hj, hjs⟩ := tl_surj F hemp s'
    apply hnone1 (tl F hemp (j + 1))
    have := tl_adj F hemp j
    rw [hjs] at this
    exact this.trans hQ
  -- the relabelled tile
  haveI : HasFansC (relabel D σ).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hidx' := relabel_hidx D idx σ hidx
  have hnc' : NotComb (slen (relabel D σ) 0) (slen (relabel D σ) 1) (slen (relabel D σ) 2) := by
    rw [relabel_slen, relabel_slen, relabel_slen]; exact hnc
  have hxor : (nsq (F.q x) = slen (relabel D σ) 0 ^ 2 ∧ nsq (F.p y) ≠ slen (relabel D σ) 0 ^ 2) ∨
      (nsq (F.q x) ≠ slen (relabel D σ) 0 ^ 2 ∧ nsq (F.p y) = slen (relabel D σ) 0 ^ 2) := by
    rw [relabel_slen, hq, hp]
    rcases hone with h | h
    · left
      refine ⟨by rw [h], ?_⟩
      exact hsq _ (fun h' => hne (by rw [h, h']))
    · right
      refine ⟨?_, by rw [h]⟩
      exact hsq _ (fun h' => hne (by rw [h, h']))
  obtain ⟨H', hH'⟩ := ga_edge_of_ray (relabel D σ) (relabelIdx idx σ) hidx' hnc' F x y (hcor x) (hcor y) hxy hnb hxor
  refine ⟨H', ?_⟩
  rw [relabel_slen] at hH'
  exact hH'

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.g1_of_centre
