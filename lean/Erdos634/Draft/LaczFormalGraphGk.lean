-- Draft/LaczFormalGraphGk.lean -- D5 (part 4): the head of a `Gamma_k` edge has a complete fan of six corner tiles, types (2,2,2) or (3,3,0), and the
-- tile weights `(w0,w1,w2)` of the three equilateral-target tiles.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), proof of Lemma 8.1(i): "the equation at X is 2a+2b+2g = 2pi or 3a+3b = 2pi").
import Erdos634.Draft.LaczFormalGraphFull
import Erdos634.Draft.LaczFormalRegFan

open scoped Classical
open Erdos634.Geometry Erdos634.KConj

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- The model angles are `w_i * u`, with `α + β = 2γ` (weights `(1,7,4)`, `(1,19,10)`, `(7,13,10)` times `π/12`, `π/30`, `π/30`). -/
structure WtData (D : CongruentDissection N) (w0 w1 w2 : ℕ) (u : ℝ) : Prop where
  hu : 0 < u
  h0 : D.model.angleAt 0 = w0 * u
  h1 : D.model.angleAt 1 = w1 * u
  h2 : D.model.angleAt 2 = w2 * u
  hsum : ((w0 + w1 + w2 : ℕ) : ℝ) * u = Real.pi
  hw : w0 + w1 = 2 * w2
  hw2 : 0 < w2

theorem WtData.eq_nat {D : CongruentDissection N} {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    (n0 n1 n2 k : ℕ) (h : (n0 : ℝ) * D.model.angleAt 0 + n1 * D.model.angleAt 1 + n2 * D.model.angleAt 2 = k * Real.pi) :
    n0 * w0 + n1 * w1 + n2 * w2 = k * (w0 + w1 + w2) := by
  rw [W.h0, W.h1, W.h2, ← W.hsum] at h
  have hu := W.hu
  have : ((n0 * w0 + n1 * w1 + n2 * w2 : ℕ) : ℝ) * u = ((k * (w0 + w1 + w2) : ℕ) : ℝ) * u := by
    push_cast at h ⊢; linarith
  exact_mod_cast mul_right_cancel₀ hu.ne' this

/-- Regularity `#α = #β` plus `n0 w0 + n1 w1 + n2 w2 = k (w0+w1+w2)`: `2 p + r = 3 k`. -/
theorem WtData.reg_eq {D : CongruentDissection N} {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    {p r k : ℕ} (h : p * w0 + p * w1 + r * w2 = k * (w0 + w1 + w2)) : 2 * p + r = 3 * k := by
  have hw := W.hw
  have hw2 := W.hw2
  have h1 : (2 * p + r) * w2 = (3 * k) * w2 := by
    have e1 : p * w0 + p * w1 = p * (2 * w2) := by rw [← hw]; ring
    have e2 : k * (w0 + w1 + w2) = k * (3 * w2) := by rw [show w0 + w1 + w2 = 3 * w2 by omega]
    calc (2 * p + r) * w2 = p * (2 * w2) + r * w2 := by ring
      _ = p * w0 + p * w1 + r * w2 := by rw [← e1]
      _ = k * (3 * w2) := by rw [h, e2]
      _ = 3 * k * w2 := by ring
  exact Nat.eq_of_mul_eq_mul_right hw2 h1

theorem halfPlaneArith_of_wt {D : CongruentDissection N} {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u) : HalfPlaneArith D := by
  intro n0 n1 n2 h hn
  subst hn
  have h1 := W.eq_nat n0 n0 n2 1 (by simpa using h)
  have h2 := W.reg_eq (k := 1) (by simpa using h1)
  omega

theorem model_angle_pos (D : CongruentDissection N) (l : Fin 3) : 0 < D.model.angleAt l :=
  Erdos634.MarchFlank.cornerAngle_pos D.model l

/-- **The head of a `Γ_k` edge has a complete fan of six corner tiles** with types `(3,3,0)` or `(2,2,2)`. -/
theorem gk_fan_full (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    {Z X : Plane} (hE : GkEdge D.toDissection idx Z X) (hreg : cnt D idx X 0 = cnt D idx X 1) :
    ∃ (κ : Type) (_ : Fintype κ) (F : ExtFan D.toDissection X κ) (hemp : IsEmpty κ),
      (∀ x : AtV D.toDissection X, 0 < crs (F.p x) (F.q x)) ∧ Fintype.card (AtV D.toDissection X) = 6 ∧
      ((cnt D idx X 0 = 3 ∧ cnt D idx X 1 = 3 ∧ cnt D idx X 2 = 0) ∨ (cnt D idx X 0 = 2 ∧ cnt D idx X 1 = 2 ∧ cnt D idx X 2 = 2)) := by
  classical
  have hX : ∃ i k, (D.tile i).pts k = X := by
    obtain ⟨i, j, k1, k2, k1', k2', -, -, a2, -⟩ := hE
    exact ⟨i, k2, a2⟩
  have hb := gk_two_beta D idx hE
  obtain ⟨κ, _, ⟨F⟩⟩ := extFan_exists D.toDissection X hX
  have hsum := head_angle_sum_gen D idx hidxA F
  rw [Fin.sum_univ_three] at hsum
  set c0 := cnt D idx X 0 with hc0
  set c1 := cnt D idx X 1 with hc1
  set c2 := cnt D idx X 2 with hc2
  have hA0 := model_angle_pos D 0
  have hA1 := model_angle_pos D 1
  have hA2 := model_angle_pos D 2
  have hc0' : (2 : ℝ) ≤ c0 := by exact_mod_cast (hreg ▸ hb : 2 ≤ c0)
  have hc1' : (2 : ℝ) ≤ c1 := by exact_mod_cast hb
  have hpi : Real.pi = 3 * (w2 : ℝ) * u := by
    have := W.hsum
    have hw : ((w0 + w1 + w2 : ℕ) : ℝ) = 3 * w2 := by
      have : w0 + w1 + w2 = 3 * w2 := by have := W.hw; omega
      rw [this]; push_cast; ring
    rw [← this, hw]
  have hA01 : D.model.angleAt 0 + D.model.angleAt 1 = 2 * w2 * u := by
    rw [W.h0, W.h1]
    have : (w0 : ℝ) + w1 = 2 * w2 := by exact_mod_cast W.hw
    linear_combination u * this
  have hSge : 4 * (w2 : ℝ) * u ≤ ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l := by
    rw [Fin.sum_univ_three]
    have t0 : (c0 : ℝ) * D.model.angleAt 0 ≥ 2 * D.model.angleAt 0 := by nlinarith
    have t1 : (c1 : ℝ) * D.model.angleAt 1 ≥ 2 * D.model.angleAt 1 := by nlinarith
    have t2 : (c2 : ℝ) * D.model.angleAt 2 ≥ 0 := mul_nonneg (Nat.cast_nonneg c2) hA2.le
    linarith [hA01]
  have hw2pos : (0 : ℝ) < w2 := by exact_mod_cast W.hw2
  have hupos := W.hu
  have hpos4 : 0 < (w2 : ℝ) * u := mul_pos hw2pos hupos
  obtain ⟨hvg⟩ : Nonempty (True) := ⟨trivial⟩
  have hS2 : ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l = 2 * Real.pi := by
    rcases vertex_group D idx hidxA X (by obtain ⟨i, k, hk⟩ := hX; exact ⟨(i, k), hk⟩) with ⟨j, -, hj⟩ | ⟨-, hj | hj⟩
    · exfalso
      have hlt : D.target.angleAt j < Real.pi := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target j
      rw [hj] at hSge; nlinarith
    · exfalso; rw [hj] at hSge; nlinarith
    · exact hj
  have hS2' : (c0 : ℝ) * D.model.angleAt 0 + c1 * D.model.angleAt 1 + c2 * D.model.angleAt 2 = 2 * Real.pi := by
    rw [Fin.sum_univ_three] at hS2; exact hS2
  rw [hS2'] at hsum
  have hvirt : 0 ≤ ∑ j, wd (F.pe j) (F.qe j) := Finset.sum_nonneg (fun j _ => (wd_pos (F.hokE j)).le)
  have hStr : (Strn D.toDissection X).card = 0 := by
    have hcn : (0 : ℝ) ≤ ((Strn D.toDissection X).card : ℝ) := Nat.cast_nonneg _
    have hp := Real.pi_pos
    have : Real.pi * ((Strn D.toDissection X).card : ℝ) = 0 := by nlinarith
    have h0 : ((Strn D.toDissection X).card : ℝ) = 0 := (mul_eq_zero.mp this).resolve_left hp.ne'
    exact_mod_cast h0
  have hv0 : ∑ j, wd (F.pe j) (F.qe j) = 0 := by
    have : Real.pi * ((Strn D.toDissection X).card : ℝ) = 0 := by rw [hStr]; simp
    linarith
  have hemp : IsEmpty κ := by
    refine ⟨fun j => ?_⟩
    have h1 := Finset.single_le_sum (f := fun j => wd (F.pe j) (F.qe j)) (fun j _ => (wd_pos (F.hokE j)).le) (Finset.mem_univ j)
    have h2 := wd_pos (F.hokE j)
    simp only at h1
    linarith
  have hcorner : ∀ x : AtV D.toDissection X, 0 < crs (F.p x) (F.q x) := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, -⟩
    · exact crs_pos_of_corner (F.hok x) (F.hspec x) ⟨k, hk⟩
    · exfalso
      have : x.1 ∈ Strn D.toDissection X := by
        simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨x.2, hnv⟩
      have := Finset.card_pos.mpr ⟨x.1, this⟩
      omega
  have hnat := W.eq_nat c0 c1 c2 2 (by rw [hS2']; push_cast; ring)
  have hreg2 := W.reg_eq (p := c0) (r := c2) (k := 2) (by rw [← hreg] at hnat; exact hnat)
  have hcard : Fintype.card (AtV D.toDissection X) = 6 := by
    rw [card_atV, card_corn D idx X, hStr, Fin.sum_univ_three]
    omega
  refine ⟨κ, inferInstance, F, hemp, hcorner, hcard, ?_⟩
  omega

theorem cnt_atv (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X : Plane}
    (k : AtV D.toDissection X → Fin 3) (hk : ∀ x, (D.tile x.1).pts (k x) = X) (l : Fin 3) :
    cnt D idx X l = (Finset.univ.filter (fun x : AtV D.toDissection X => idx x.1 (k x) = l)).card := by
  classical
  unfold cnt
  symm
  refine Finset.card_bij (fun x _ => (x.1, k x)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hk x, hx⟩
  · intro x _ y _ h
    exact Subtype.ext (congrArg Prod.fst h)
  · rintro ⟨i, k'⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hmem : X ∈ (D.tile i).carrier := vertex_mem hp.1
    refine ⟨⟨i, hmem⟩, ?_, ?_⟩
    · have : k ⟨i, hmem⟩ = k' := (D.tile i).indep.injective ((hk ⟨i, hmem⟩).trans hp.1.symm)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [this]; exact hp.2
    · have : k ⟨i, hmem⟩ = k' := (D.tile i).indep.injective ((hk ⟨i, hmem⟩).trans hp.1.symm)
      simp [this]

theorem list_filter_len {α : Type*} (f : ℕ → α) (p : α → Bool) (m : ℕ) :
    (((List.range m).map f).filter p).length = ∑ s ∈ Finset.range m, if p (f s) = true then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    congr 1
    by_cases h : p (f m) = true <;> simp [h]


section CD

variable (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X : Plane} {κ : Type} [Fintype κ]
  (F : ExtFan D.toDissection X κ) (hcor : ∀ x : AtV D.toDissection X, 0 < crs (F.p x) (F.q x))

include hcor

theorem cd_ex (x : AtV D.toDissection X) :
    ∃ p : Fin 3 × Bool, (D.tile x.1).pts p.1 = X ∧ F.p x = toV2 ((D.tile x.1).pts (armP p.1 p.2) - X) ∧
      F.q x = toV2 ((D.tile x.1).pts (armQ p.1 p.2) - X) := by
  obtain ⟨k, hk⟩ := F.corner_of_crs x (hcor x)
  obtain ⟨kk, fl, h1, h2, h3⟩ := spec_corner_data (F.hspec x) ⟨k, hk⟩
  exact ⟨(kk, fl), h1, h2, h3⟩

/-- Canonical corner data of a corner sector. -/
noncomputable def cd (x : AtV D.toDissection X) : Fin 3 × Bool := Classical.choose (cd_ex D F hcor x)

theorem cd_spec (x : AtV D.toDissection X) :
    (D.tile x.1).pts (cd D F hcor x).1 = X ∧ F.p x = toV2 ((D.tile x.1).pts (armP (cd D F hcor x).1 (cd D F hcor x).2) - X) ∧
      F.q x = toV2 ((D.tile x.1).pts (armQ (cd D F hcor x).1 (cd D F hcor x).2) - X) :=
  Classical.choose_spec (cd_ex D F hcor x)

/-- The code of a corner sector. -/
noncomputable def cdcode (x : AtV D.toDissection X) : ℕ := codeOf (idx x.1) (cd D F hcor x).1 (cd D F hcor x).2

theorem cdcode_spec (x : AtV D.toDissection X) :
    RegFan.tT (cdcode D idx F hcor x) = (idx x.1 (cd D F hcor x).1 : ℕ) ∧
    RegFan.tU (cdcode D idx F hcor x) = (idx x.1 (armP (cd D F hcor x).1 (cd D F hcor x).2) : ℕ) ∧
    RegFan.tW (cdcode D idx F hcor x) = (idx x.1 (armQ (cd D F hcor x).1 (cd D F hcor x).2) : ℕ) ∧
    cdcode D idx F hcor x < 6 :=
  codeOf_spec' (idx x.1) _ _

/-- The cyclic list of codes of `m` consecutive sectors from base index `b`. -/
noncomputable def lst (hemp : IsEmpty κ) (b : ℕ) : List ℕ :=
  (List.range (Fintype.card (AtV D.toDissection X))).map (fun s => cdcode D idx F hcor (tl F hemp (b + s)))

theorem lst_length (hemp : IsEmpty κ) (b : ℕ) : (lst D idx F hcor hemp b).length = Fintype.card (AtV D.toDissection X) := by
  simp [lst]

theorem lst_getD (hemp : IsEmpty κ) (b s : ℕ) (hs : s < Fintype.card (AtV D.toDissection X)) :
    (lst D idx F hcor hemp b).getD s 0 = cdcode D idx F hcor (tl F hemp (b + s)) := by
  simp [lst, List.getD_eq_getElem?_getD, hs]

theorem lst_lt (hemp : IsEmpty κ) (b : ℕ) : ∀ x ∈ lst D idx F hcor hemp b, x < 6 := by
  intro x hx
  simp only [lst, List.mem_map, List.mem_range] at hx
  obtain ⟨s, -, rfl⟩ := hx
  exact (cdcode_spec D idx F hcor _).2.2.2

theorem lst_cnt (hemp : IsEmpty κ) (b : ℕ) (j : Fin 3) :
    RegFan.cnt (lst D idx F hcor hemp b) (j : ℕ) = cnt D idx X j := by
  classical
  rw [cnt_atv D idx (fun x => (cd D F hcor x).1) (fun x => (cd_spec D F hcor x).1) j]
  unfold RegFan.cnt lst
  rw [list_filter_len, Finset.card_filter]
  have := sum_tl F hemp (fun x : AtV D.toDissection X => if (idx x.1 (cd D F hcor x).1 : Fin 3) = j then 1 else 0) b
  rw [← this]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have h := (cdcode_spec D idx F hcor (tl F hemp (b + s))).1
  simp only [h, beq_iff_eq]
  congr 1
  simp [Fin.ext_iff]

/-- Two corner sectors with the same ending ray coincide. -/
theorem corner_end_unique {x y : AtV D.toDissection X} (hx : 0 < crs (F.p x) (F.q x)) (hy : 0 < crs (F.p y) (F.q y))
    (hpar : Par (F.q x) (F.q y)) : x = y := by
  classical
  by_contra hne
  obtain ⟨δx, hδx, Hx⟩ := minus_ray_int (F.hok x)
  obtain ⟨δy, hδy, Hy⟩ := minus_ray_int (F.hok y)
  obtain ⟨c, hc, hcd⟩ := hpar.smul
  set ε := min δx δy / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hεx : ε < δx := by have := min_le_left δx δy; linarith
  have hεy : ε < δy := by have := min_le_right δx δy; linarith
  have hzx := Hx ε hε0 hεx
  have hzy := Hy ε hε0 hεy
  have hzeq : zminus (F.q x) ε = (c * (zminus (F.q y) ε).1, c * (zminus (F.q y) ε).2) := by
    unfold zminus; rw [hcd]; ext <;> simp <;> ring
  rw [hzeq] at hzx
  have hzy' := (inInt_smul hc hzy)
  exact F.disj_all (o1 := Sum.inl x) (o2 := Sum.inl y) (fun h => hne (Sum.inl.inj h)) _ ⟨by simpa using hzx, by simpa using hzy'⟩

/-- A tile at `X` having `X` (type `1`) and `Z` (type `2`) as vertices: its sector at `X` has an arm along `Z - X`, on the `q` side (then the far end has type `2`)
or on the `p` side. -/
theorem gk_side (x : AtV D.toDissection X) {Z : Plane} {kv kz : Fin 3} (hkv : (D.tile x.1).pts kv = X) (hkz : (D.tile x.1).pts kz = Z)
    (hne : kz ≠ kv) (e1 : idx x.1 kv = 1) (e2 : idx x.1 kz = 2) :
    (F.q x = toV2 (Z - X) ∧ idx x.1 (cd D F hcor x).1 = 1 ∧ idx x.1 (armQ (cd D F hcor x).1 (cd D F hcor x).2) = 2) ∨
    (F.p x = toV2 (Z - X) ∧ idx x.1 (cd D F hcor x).1 = 1 ∧ idx x.1 (armP (cd D F hcor x).1 (cd D F hcor x).2) = 2) := by
  obtain ⟨hk, hp, hq⟩ := cd_spec D F hcor x
  have hkk : (cd D F hcor x).1 = kv := (D.tile x.1).indep.injective (hk.trans hkv.symm)
  have hne' : kz ≠ (cd D F hcor x).1 := by rw [hkk]; exact hne
  rcases arm_cases (cd D F hcor x).1 (cd D F hcor x).2 kz hne' with h | h
  · right
    refine ⟨?_, by rw [hkk]; exact e1, by rw [← h]; exact e2⟩
    rw [hp, ← h, hkz]
  · left
    refine ⟨?_, by rw [hkk]; exact e1, by rw [← h]; exact e2⟩
    rw [hq, ← h, hkz]

/-- **The two tiles of a `Γ_k` edge are consecutive sectors of the fan**: some `n` has `tl n` with `β` at `X` and `γ` at the far end of its `q`-arm, and `tl (n+1)`
with `β` at `X` and `γ` at the far end of its `p`-arm. -/
theorem gk_adj (hemp : IsEmpty κ) {Z : Plane} (hE : GkEdge D.toDissection idx Z X) :
    ∃ n : ℕ, idx (tl F hemp n).1 (cd D F hcor (tl F hemp n)).1 = 1 ∧
      idx (tl F hemp n).1 (armQ (cd D F hcor (tl F hemp n)).1 (cd D F hcor (tl F hemp n)).2) = 2 ∧
      idx (tl F hemp (n + 1)).1 (cd D F hcor (tl F hemp (n + 1))).1 = 1 ∧
      idx (tl F hemp (n + 1)).1 (armP (cd D F hcor (tl F hemp (n + 1))).1 (cd D F hcor (tl F hemp (n + 1))).2) = 2 := by
  classical
  obtain ⟨i, j, k1, k2, k1', k2', hij, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hE
  set xi : AtV D.toDissection X := ⟨i, vertex_mem a2⟩
  set xj : AtV D.toDissection X := ⟨j, vertex_mem a4⟩
  have hk12 : k1 ≠ k2 := fun h => by rw [h] at a5; rw [a5] at a6; exact absurd a6 (by decide)
  have hk12' : k1' ≠ k2' := fun h => by rw [h] at a7; rw [a7] at a8; exact absurd a8 (by decide)
  have si := gk_side D idx F hcor xi (kv := k2) (kz := k1) a2 a1 hk12 a6 a5
  have sj := gk_side D idx F hcor xj (kv := k2') (kz := k1') a4 a3 hk12' a8 a7
  -- the common direction `Z - X`
  have hv : toV2 ((D.tile i).pts k1 - X) = toV2 ((D.tile j).pts k1' - X) := by rw [a1, a3]
  have hvi : (D.tile i).pts k1 = (D.tile j).pts k1' := by rw [a1, a3]
  -- consecutive sectors
  have succ_of : ∀ (x y : AtV D.toDissection X), Par (F.p y) (F.q x) → ∃ n, tl F hemp n = x ∧ tl F hemp (n + 1) = y := by
    intro x y hxy
    obtain ⟨j0, -, hj0⟩ := tl_surj F hemp x
    refine ⟨j0, hj0, ?_⟩
    have h1 := tl_adj F hemp j0
    rw [hj0] at h1
    have h2 : Par (F.p (tl F hemp (j0 + 1))) (F.p y) := h1.trans hxy.symm
    exact corner_start_unique F (hcor _) (hcor _) h2
  have hZX : Z - X ≠ 0 := by
    intro h0
    have : Z = X := sub_eq_zero.mp h0
    have h1 : (D.tile i).pts k1 = (D.tile i).pts k2 := by rw [a1, a2, this]
    exact hk12 ((D.tile i).indep.injective h1)
  have hv0 : toV2 (Z - X) ≠ 0 := toV2_ne_zero hZX
  have hrefl := par_refl hv0
  rcases si with ⟨hqi, ei1, ei2⟩ | ⟨hpi, ei1, ei2⟩ <;> rcases sj with ⟨hqj, ej1, ej2⟩ | ⟨hpj, ej1, ej2⟩
  · exfalso
    have : xi = xj := corner_end_unique D F hcor (hcor xi) (hcor xj) (by rw [hqi, hqj]; exact hrefl)
    exact hij (congrArg Subtype.val this)
  · -- xi then xj
    obtain ⟨n, hn1, hn2⟩ := succ_of xi xj (by rw [hpj, hqi]; exact hrefl)
    exact ⟨n, by rw [hn1]; exact ei1, by rw [hn1]; exact ei2, by rw [hn2]; exact ej1, by rw [hn2]; exact ej2⟩
  · -- xj then xi
    obtain ⟨n, hn1, hn2⟩ := succ_of xj xi (by rw [hpi, hqj]; exact hrefl)
    exact ⟨n, by rw [hn1]; exact ej1, by rw [hn1]; exact ej2, by rw [hn2]; exact ei1, by rw [hn2]; exact ei2⟩
  · exfalso
    have : xi = xj := corner_start_unique F (hcor xi) (hcor xj) (by rw [hpi, hpj]; exact hrefl)
    exact hij (congrArg Subtype.val this)

omit hcor in
theorem wv_angle {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u) (l : Fin 3) :
    D.model.angleAt l = (RegFan.wv (w0, w1, w2) (l : ℕ) : ℝ) * u := by
  fin_cases l
  · simpa [RegFan.wv] using W.h0
  · simpa [RegFan.wv] using W.h1
  · simpa [RegFan.wv] using W.h2

theorem wd_cd (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    (x : AtV D.toDissection X) :
    wd (F.p x) (F.q x) = (RegFan.wv (w0, w1, w2) (idx x.1 (cd D F hcor x).1 : ℕ) : ℝ) * u := by
  obtain ⟨hk, -, -⟩ := cd_spec D F hcor x
  have h1 : wd (F.p x) (F.q x) = (D.tile x.1).angleAt (cd D F hcor x).1 := by
    rw [F.hwd x]
    have e := Tri.localAngle_vertex (D.tile x.1) (cd D F hcor x).1
    rw [hk] at e
    have e2 : (D.tile x.1).angleAt (cd D F hcor x).1 =
        cornerAngle ((D.tile x.1).pts ((cd D F hcor x).1 + 1)) X ((D.tile x.1).pts ((cd D F hcor x).1 + 2)) := by
      unfold Tri.angleAt; rw [hk]
    rw [e2]; exact e
  rw [h1, ← hidxA, wv_angle D W]

omit hcor in
theorem par_not_neg {u v : V2} (h1 : Par u v) (h2 : Par u (neg2 v)) : False := by
  have a := h1.2
  have b := h2.2
  unfold dt neg2 at b
  unfold dt at a
  simp only at b
  nlinarith

/-- **An opposite ray forces the collinearity flag.**  If some sector starts along the direction opposite to the ray `i` of the fan (the ray between the sectors
`b + (i+m-1) % m` and `b + i`), then a block of consecutive corners from ray `i` has total weight `w0+w1+w2` (= `π`). -/
theorem opp_col (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    (hemp : IsEmpty κ) (b i : ℕ) (hi : i < Fintype.card (AtV D.toDissection X)) (s : AtV D.toDissection X)
    (hs : Par (F.p s) (neg2 (F.q (tl F hemp (b + (i + Fintype.card (AtV D.toDissection X) - 1) % Fintype.card (AtV D.toDissection X)))))) :
    RegFan.col (w0, w1, w2) (w0 + w1 + w2) (lst D idx F hcor hemp b) i = true := by
  classical
  set m := Fintype.card (AtV D.toDissection X) with hm
  have hpos : 0 < m := card_pos_atV F hemp
  set ρ := F.q (tl F hemp (b + (i + m - 1) % m)) with hρ
  set c := b + i with hc
  have hadj : Par (F.p (tl F hemp c)) ρ := by
    have h := tl_adj F hemp (b + (i + m - 1) % m)
    rw [tl_ray F hemp b i hi] at h
    exact h
  obtain ⟨m', hm', hsm⟩ := tl_shift_surj F hemp c s
  have hm0 : m' ≠ 0 := by
    rintro rfl
    simp only [add_zero] at hsm
    rw [hsm] at hadj
    exact par_not_neg hadj hs
  -- the chain of sectors from ray `i`
  set u' : ℕ → V2 := fun t => F.p (tl F hemp (c + t)) with hu'
  set v' : ℕ → V2 := fun t => F.q (tl F hemp (c + t)) with hv'
  have hu0 : ∀ t, u' t ≠ 0 := fun t => (F.hok _).ne_p
  have hpar : ∀ t, Par (u' (t + 1)) (v' t) := fun t => tl_adj F hemp (c + t)
  have hopp : ∃ t : ℝ, 0 < t ∧ u' m' = (-(t * (u' 0).1), -(t * (u' 0).2)) := by
    have hum : Par (u' m') (neg2 ρ) := by simp only [hu']; rw [hsm]; exact hs
    have hu0' : Par (u' 0) ρ := by simpa [hu'] using hadj
    obtain ⟨a, ha, hau⟩ := hum.smul
    obtain ⟨b', hb', hbu⟩ := hu0'.smul
    refine ⟨a / b', div_pos ha hb', ?_⟩
    rw [hau, hbu]
    unfold neg2
    ext <;> simp <;> field_simp
  have htot : ∑ t ∈ Finset.range m, wd (u' t) (v' t) = 2 * Real.pi := by
    have h1 := sum_tl F hemp (fun x : AtV D.toDissection X => wd (F.p x) (F.q x)) c
    have h2 := F.hsum
    have hv : ∑ j, wd (F.pe j) (F.qe j) = 0 := by haveI := hemp; simp
    rw [hv, add_zero] at h2
    simpa [hu', hv'] using h1.trans h2
  have hSpos : 0 < ∑ t ∈ Finset.range m', wd (u' t) (v' t) := by
    apply Finset.sum_pos
    · intro t _; exact wd_pos (F.hok _)
    · exact ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hm0)⟩
  have hSlt : ∑ t ∈ Finset.range m', wd (u' t) (v' t) < 2 * Real.pi := by
    rw [← htot, ← Finset.sum_range_add_sum_Ico (fun t => wd (u' t) (v' t)) (le_of_lt hm')]
    have : 0 < ∑ t ∈ Finset.Ico m' m, wd (u' t) (v' t) := by
      apply Finset.sum_pos
      · intro t _; exact wd_pos (F.hok _)
      · exact ⟨m', Finset.mem_Ico.mpr ⟨le_rfl, hm'⟩⟩
    linarith
  have hπ := opp_sum u' v' hu0 hpar m' hopp hSpos hSlt
  -- convert to weights
  unfold RegFan.col
  rw [List.any_eq_true]
  refine ⟨m', List.mem_range.mpr (by rw [lst_length]; exact hm'), ?_⟩
  simp only [beq_iff_eq]
  unfold RegFan.sect
  have hlen := lst_length D idx F hcor hemp b
  have key : ∀ t ∈ Finset.range m', wd (u' t) (v' t) = u * (RegFan.wv (w0, w1, w2) (RegFan.tT ((lst D idx F hcor hemp b).getD ((i + t) % (lst D idx F hcor hemp b).length) 0)) : ℝ) := by
    intro t _
    rw [hlen, ← hm]
    have hlt : (i + t) % m < m := Nat.mod_lt _ hpos
    rw [lst_getD D idx F hcor hemp b _ hlt, (cdcode_spec D idx F hcor _).1]
    have hx : tl F hemp (b + (i + t) % m) = tl F hemp (c + t) := by
      have h := (Nat.mod_modEq (i + t) m).add_left b
      have e : tl F hemp (b + (i + t) % m) = tl F hemp (b + (i + t)) := by
        rw [tl_mod F hemp (b + (i + t) % m), tl_mod F hemp (b + (i + t))]
        exact congrArg _ h
      rw [e, hc, add_assoc]
    rw [hx]
    have := wd_cd D idx F hcor hidxA W (tl F hemp (c + t))
    simp only [hu', hv']
    rw [this]; ring
  have hsum : ∑ t ∈ Finset.range m', wd (u' t) (v' t) = u * ((((List.range m').map fun t => RegFan.wv (w0, w1, w2) (RegFan.tT ((lst D idx F hcor hemp b).getD ((i + t) % (lst D idx F hcor hemp b).length) 0))).sum : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
    congr 1
    have e : (((List.range m').map fun t => RegFan.wv (w0, w1, w2) (RegFan.tT ((lst D idx F hcor hemp b).getD ((i + t) % (lst D idx F hcor hemp b).length) 0))).sum : ℕ) = ∑ t ∈ Finset.range m', RegFan.wv (w0, w1, w2) (RegFan.tT ((lst D idx F hcor hemp b).getD ((i + t) % (lst D idx F hcor hemp b).length) 0)) := rfl
    rw [e, Nat.cast_sum]
  rw [hπ] at hsum
  have hu := W.hu
  have h2 : u * (((w0 + w1 + w2 : ℕ)) : ℝ) = u * (((List.range m').map fun t => RegFan.wv (w0, w1, w2) (RegFan.tT ((lst D idx F hcor hemp b).getD ((i + t) % (lst D idx F hcor hemp b).length) 0))).sum : ℕ) := by
    rw [← hsum, mul_comm, W.hsum]
  have h3 := mul_left_cancel₀ hu.ne' h2
  exact_mod_cast h3.symm

/-- **No collinear ray ⇒ `NoBack`**: if the flag `col` of ray `i` is false, no step along the ray passes through or ends at `X` from the other side. -/
theorem noBack_of_nocol (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    (hemp : IsEmpty κ) (b i : ℕ) (hi : i < Fintype.card (AtV D.toDissection X))
    (hcol : RegFan.col (w0, w1, w2) (w0 + w1 + w2) (lst D idx F hcor hemp b) i = false) :
    NoBack D.toDissection (F.q (tl F hemp (b + (i + Fintype.card (AtV D.toDissection X) - 1) % Fintype.card (AtV D.toDissection X)))) X := by
  classical
  apply F.noBack_of_none
  intro s
  have hp : ∀ s' : AtV D.toDissection X, ¬ Par (F.p s') (neg2 (F.q (tl F hemp (b + (i + Fintype.card (AtV D.toDissection X) - 1) % Fintype.card (AtV D.toDissection X))))) := by
    intro s' h
    have := opp_col D idx F hcor hidxA W hemp b i hi s' h
    rw [hcol] at this
    exact absurd this (by simp)
  refine ⟨hp s, fun h => ?_⟩
  obtain ⟨j0, -, hj0⟩ := tl_surj F hemp s
  have h1 := tl_adj F hemp j0
  rw [hj0] at h1
  exact hp _ (h1.trans h)

end CD

/-- **Lemma 8.1(i), `Γ_k` part**: the head `X` of an edge of `Γ_k` is the tail of an edge of `Γ_a` or of `Γ_k` (for the three weight triples of the equilateral-target tiles),
provided the counts at `X` are regular. -/
theorem gk_head_out (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    (hw3 : (w0, w1, w2) = (1, 7, 4) ∨ (w0, w1, w2) = (1, 19, 10) ∨ (w0, w1, w2) = (7, 13, 10))
    {Z X : Plane} (hE : GkEdge D.toDissection idx Z X) (hreg : cnt D idx X 0 = cnt D idx X 1) :
    (∃ H', GaEdge D.toDissection (slen D 0) X H') ∨ ∃ Z', GkEdge D.toDissection idx X Z' := by
  classical
  obtain ⟨κ, _, F, hemp, hcor, hcard6, hcls⟩ := gk_fan_full D idx hidxA W hE hreg
  obtain ⟨n, e1, e2, e3, e4⟩ := gk_adj D idx F hcor hemp hE
  set l := lst D idx F hcor hemp n with hl
  have hlen : l.length = 6 := by rw [hl, lst_length, hcard6]
  have hlt := lst_lt D idx F hcor hemp n
  have hc0 : RegFan.cnt l 0 = cnt D idx X 0 := lst_cnt D idx F hcor hemp n 0
  have hc1 : RegFan.cnt l 1 = cnt D idx X 1 := lst_cnt D idx F hcor hemp n 1
  have hc2 : RegFan.cnt l 2 = cnt D idx X 2 := lst_cnt D idx F hcor hemp n 2
  have hL1 : RegFan.Lc l 1 = cdcode D idx F hcor (tl F hemp n) := by
    unfold RegFan.Lc; rw [hlen]
    have := lst_getD D idx F hcor hemp n 0 (by rw [hcard6]; norm_num)
    simpa using this
  have hR1 : RegFan.Rc l 1 = cdcode D idx F hcor (tl F hemp (n + 1)) := by
    unfold RegFan.Rc; rw [hlen]
    have := lst_getD D idx F hcor hemp n 1 (by rw [hcard6]; norm_num)
    simpa using this
  have hany : (List.range 6).any (fun i => RegFan.tT (RegFan.Lc l i) == 1 && RegFan.tT (RegFan.Rc l i) == 1 &&
      RegFan.tW (RegFan.Lc l i) == 2 && RegFan.tU (RegFan.Rc l i) == 2) = true := by
    rw [List.any_eq_true]
    refine ⟨1, by simp, ?_⟩
    obtain ⟨a1, -, a3, -⟩ := cdcode_spec D idx F hcor (tl F hemp n)
    obtain ⟨b1, b2, -, -⟩ := cdcode_spec D idx F hcor (tl F hemp (n + 1))
    simp only [hL1, hR1, a1, a3, b1, b2, e1, e2, e3, e4, Bool.and_eq_true, beq_iff_eq]
    simp
  have hhyp : (RegFan.fullHyp333 l || RegFan.fullHyp222 l) = true := by
    rcases hcls with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · have : RegFan.fullHyp333 l = true := by
        unfold RegFan.fullHyp333
        rw [hc0, hc1, hc2, h0, h1, h2]
        simpa [RegFan.fullHyp333] using hany
      simp [this]
    · have : RegFan.fullHyp222 l = true := by
        unfold RegFan.fullHyp222
        rw [hc0, hc1, hc2, h0, h1, h2]
        simpa [RegFan.fullHyp222] using hany
      simp [this]
  have hconcl := RegFan.full_fan_gk_head (w0, w1, w2) hw3 l hlen hlt hhyp
  unfold RegFan.fullConcl at hconcl
  rw [List.any_eq_true] at hconcl
  obtain ⟨i, hi6, hi⟩ := hconcl
  have hi' : i < Fintype.card (AtV D.toDissection X) := by rw [hcard6]; exact List.mem_range.mp hi6
  set x := tl F hemp (n + (i + Fintype.card (AtV D.toDissection X) - 1) % Fintype.card (AtV D.toDissection X)) with hx
  set y := tl F hemp (n + i) with hy
  have hxy : Par (F.p y) (F.q x) := by
    have h := tl_adj F hemp (n + (i + Fintype.card (AtV D.toDissection X) - 1) % Fintype.card (AtV D.toDissection X))
    rw [tl_ray F hemp n i hi'] at h
    exact h
  have hne : x ≠ y := by
    intro h
    have h1 := tl_ray F hemp n i hi'
    have h2 : tl F hemp (n + (i + Fintype.card (AtV D.toDissection X) - 1) % Fintype.card (AtV D.toDissection X)) =
        tl F hemp (n + (i + Fintype.card (AtV D.toDissection X) - 1) % Fintype.card (AtV D.toDissection X) + 1) := by
      rw [h1]; exact h
    have h3 := tl_inj_mod F hemp h2
    rw [hcard6] at h3
    omega
  have hLc : RegFan.Lc l i = cdcode D idx F hcor x := by
    unfold RegFan.Lc; rw [hlen]
    have hlt' : (i + 6 - 1) % 6 < Fintype.card (AtV D.toDissection X) := by rw [hcard6]; exact Nat.mod_lt _ (by norm_num)
    rw [hl, lst_getD D idx F hcor hemp n _ hlt', hx, hcard6]
  have hRc : RegFan.Rc l i = cdcode D idx F hcor y := by
    unfold RegFan.Rc; rw [hlen]
    have hlt' : i % 6 < Fintype.card (AtV D.toDissection X) := by rw [hcard6]; exact Nat.mod_lt _ (by norm_num)
    rw [hl, lst_getD D idx F hcor hemp n _ hlt']
    have : i % 6 = i := Nat.mod_eq_of_lt (List.mem_range.mp hi6)
    rw [this]
  obtain ⟨hkx, hpx, hqx⟩ := cd_spec D F hcor x
  obtain ⟨hky, hpy, hqy⟩ := cd_spec D F hcor y
  rw [Bool.or_eq_true] at hi
  rcases hi with hi | hi
  · -- Γ_a edge along ray i
    rw [Bool.and_eq_true] at hi
    obtain ⟨hnc', hga⟩ := hi
    left
    have hcolf : RegFan.col (w0, w1, w2) (w0 + w1 + w2) l i = false := by simpa using hnc'
    have hnb := noBack_of_nocol D idx F hcor hidxA W hemp n i hi' (by rw [← hl]; exact hcolf)
    unfold RegFan.gaEdge at hga
    rw [hLc, hRc] at hga
    exact ga_of_codes D idx hidx hnc hab hac F x y (hcor x) (hcor y) hxy hnb hkx hky hqx hpy hga
  · right
    unfold RegFan.gkEdge at hi
    rw [hLc, hRc] at hi
    exact gk_of_codes D idx hidx hab hac F x y hxy hne hkx hky hpx hqx hpy hqy hi

end Erdos634.Draft.LaczFormal.Graph
