-- Draft/LaczFormalRGFull.lean -- S3 of PLAN_THM21: port of LaczFormalGraphFull to `RegionDissection` (dissection-dependent declarations only; the rest is used
-- from the original module).  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang; port of the project's LaczFormalGraphFull.
import Erdos634.Draft.LaczFormalRGCnt
import Erdos634.Draft.LaczFormalGraphFull


open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}


open scoped Classical

open Erdos634.Geometry Erdos634.KConj

section TL

variable {D : RegionDissection N} {X : Plane} {κ : Type} [Fintype κ] (F : ExtFan D X κ) (hemp : IsEmpty κ)

include F hemp

/-- The `n`-th tile sector of the cyclic fan (indices mod `m = #tiles at X`). -/
noncomputable def tl (n : ℕ) : AtV D X :=
  Sum.elim id (fun j => (hemp.false j).elim) (F.e n)


theorem e_eq (n : ℕ) : F.e n = Sum.inl (tl F hemp n) := by
  unfold tl
  rcases h : F.e n with x | j
  · simp
  · exact (hemp.false j).elim


theorem card_ext : Fintype.card (AtV D X ⊕ κ) = Fintype.card (AtV D X) := by
  haveI := hemp
  rw [Fintype.card_sum, Fintype.card_eq_zero (α := κ), add_zero]


theorem tl_add (n : ℕ) : tl F hemp (n + Fintype.card (AtV D X)) = tl F hemp n := by
  have h := F.hper n
  rw [card_ext F hemp] at h
  have := e_eq F hemp (n + Fintype.card (AtV D X))
  rw [h, e_eq F hemp n] at this
  exact (Sum.inl.inj this).symm


theorem tl_add_mul (r q : ℕ) : tl F hemp (r + Fintype.card (AtV D X) * q) = tl F hemp r := by
  induction q with
  | zero => simp
  | succ q ih =>
    have : r + Fintype.card (AtV D X) * (q + 1) = (r + Fintype.card (AtV D X) * q) + Fintype.card (AtV D X) := by ring
    rw [this, tl_add, ih]


theorem tl_mod (n : ℕ) : tl F hemp n = tl F hemp (n % Fintype.card (AtV D X)) := by
  calc tl F hemp n = tl F hemp (n % Fintype.card (AtV D X) + Fintype.card (AtV D X) * (n / Fintype.card (AtV D X))) := by
        rw [Nat.mod_add_div]
    _ = tl F hemp (n % Fintype.card (AtV D X)) := tl_add_mul F hemp _ _


theorem card_pos_atV : 0 < Fintype.card (AtV D X) := by
  haveI : Nonempty (AtV D X ⊕ κ) := ⟨F.e 0⟩
  have := Fintype.card_pos (α := AtV D X ⊕ κ)
  rwa [card_ext F hemp] at this


theorem tl_inj {a b : ℕ} (ha : a < Fintype.card (AtV D X)) (hb : b < Fintype.card (AtV D X)) (h : tl F hemp a = tl F hemp b) : a = b := by
  have h1 := F.hinj (by simpa [card_ext F hemp] using ha : a ∈ Set.Iio (Fintype.card (AtV D X ⊕ κ)))
    (by simpa [card_ext F hemp] using hb : b ∈ Set.Iio (Fintype.card (AtV D X ⊕ κ)))
    (by rw [e_eq F hemp a, e_eq F hemp b, h])
  exact h1


theorem tl_inj_mod {a b : ℕ} (h : tl F hemp a = tl F hemp b) : a % Fintype.card (AtV D X) = b % Fintype.card (AtV D X) := by
  have hpos := card_pos_atV F hemp
  rw [tl_mod F hemp a, tl_mod F hemp b] at h
  exact tl_inj F hemp (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) h


theorem tl_surj (x : AtV D X) : ∃ j < Fintype.card (AtV D X), tl F hemp j = x := by
  obtain ⟨j, hj, hej⟩ := F.hsurj (Sum.inl x)
  rw [card_ext F hemp] at hj
  refine ⟨j, hj, ?_⟩
  rw [e_eq F hemp j] at hej
  exact Sum.inl.inj hej


theorem tl_adj (n : ℕ) : Par (F.p (tl F hemp (n + 1))) (F.q (tl F hemp n)) := by
  have := F.hP n
  rw [e_eq F hemp (n + 1), e_eq F hemp n] at this
  simpa using this


/-- Sum over `m` consecutive sectors from any base index equals the sum over all tiles at `X`. -/
theorem sum_tl {M : Type*} [AddCommMonoid M] (g : AtV D X → M) (b : ℕ) :
    ∑ s ∈ Finset.range (Fintype.card (AtV D X)), g (tl F hemp (b + s)) = ∑ x : AtV D X, g x := by
  have hpos := card_pos_atV F hemp
  let φ : Fin (Fintype.card (AtV D X)) → AtV D X := fun s => tl F hemp (b + s)
  have hinj : Function.Injective φ := by
    intro s s' h
    have := tl_inj_mod F hemp h
    apply Fin.ext
    have h2 : (b + s) % Fintype.card (AtV D X) = (b + s') % Fintype.card (AtV D X) := this
    have h3 : (s : ℕ) ≡ s' [MOD Fintype.card (AtV D X)] := Nat.ModEq.add_left_cancel' b h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 s.2 s'.2
  have hbij : Function.Bijective φ := by
    refine ⟨hinj, ?_⟩
    exact (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, by simp⟩ |>.2
  rw [Finset.sum_range (fun s => g (tl F hemp (b + s)))]
  exact Fintype.sum_bijective φ hbij _ _ (fun _ => rfl)


/-- Every tile sector appears among `m` consecutive sectors from any base. -/
theorem tl_shift_surj (c : ℕ) (x : AtV D X) : ∃ s < Fintype.card (AtV D X), tl F hemp (c + s) = x := by
  have hpos := card_pos_atV F hemp
  let φ : Fin (Fintype.card (AtV D X)) → AtV D X := fun s => tl F hemp (c + s)
  have hinj : Function.Injective φ := by
    intro s s' h
    have := tl_inj_mod F hemp h
    apply Fin.ext
    have h2 : (c + s) % Fintype.card (AtV D X) = (c + s') % Fintype.card (AtV D X) := this
    have h3 : (s : ℕ) ≡ s' [MOD Fintype.card (AtV D X)] := Nat.ModEq.add_left_cancel' c h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 s.2 s'.2
  have hbij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, by simp⟩
  obtain ⟨s, hs⟩ := hbij.2 x
  exact ⟨s, s.2, hs⟩


/-- The ray between sectors `b + (i+m-1) % m` and `b + i`. -/
theorem tl_ray (b i : ℕ) (hi : i < Fintype.card (AtV D X)) :
    tl F hemp (b + (i + Fintype.card (AtV D X) - 1) % Fintype.card (AtV D X) + 1) = tl F hemp (b + i) := by
  have hpos := card_pos_atV F hemp
  set m := Fintype.card (AtV D X) with hm
  by_cases h0 : i = 0
  · subst h0
    have hlt : 0 + m - 1 < m := by omega
    have : (0 + m - 1) % m = m - 1 := by rw [Nat.mod_eq_of_lt hlt]; omega
    rw [this]
    have e : b + (m - 1) + 1 = b + m := by omega
    rw [e, tl_add]
    rfl
  · have : (i + m - 1) % m = i - 1 := by
      have e : i + m - 1 = (i - 1) + m := by omega
      rw [e, Nat.add_mod_right]
      have hlt : i - 1 < m := by omega
      exact Nat.mod_eq_of_lt hlt
    rw [this]
    have e : b + (i - 1) + 1 = b + i := by omega
    rw [e]



end TL

end Erdos634.Draft.LaczFormal.RG
