-- Draft/LaczFormalRG4Gk.lean -- Case IV (gamma = pi/3): port of the weight-free part of LaczFormalGraphGk (corner data `cd`, code lists `lst`, `gk_side`, `gk_adj`) to `RegionDissection`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), proof of Lemma 8.1), Beeson, Beeson-Zhang; port of the project's LaczFormalGraphGk.
import Erdos634.Draft.LaczFormalRG4Arith
import Erdos634.Draft.LaczFormalGraphGk
import Erdos634.Draft.LaczFormalRG4RegFan

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}


open scoped Classical

open Erdos634.Geometry Erdos634.KConj

theorem cnt_atv (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X : Plane}
    (k : AtV D.toRegionDissection X → Fin 3) (hk : ∀ x, (D.tile x.1).pts (k x) = X) (l : Fin 3) :
    cnt D idx X l = (Finset.univ.filter (fun x : AtV D.toRegionDissection X => idx x.1 (k x) = l)).card := by
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


theorem sum_by_type (m : ℕ) (ts : ℕ → Fin 3) (g : Fin 3 → ℝ) :
    ∑ t ∈ Finset.range m, g (ts t) = ∑ j : Fin 3, (((Finset.range m).filter (fun t => ts t = j)).card : ℝ) * g j := by
  have h1 : ∀ t, g (ts t) = ∑ j : Fin 3, (if ts t = j then g j else 0) := by
    intro t; simp [Finset.sum_ite_eq]
  calc ∑ t ∈ Finset.range m, g (ts t) = ∑ t ∈ Finset.range m, ∑ j : Fin 3, (if ts t = j then g j else 0) := Finset.sum_congr rfl (fun t _ => h1 t)
    _ = ∑ j : Fin 3, ∑ t ∈ Finset.range m, (if ts t = j then g j else 0) := Finset.sum_comm
    _ = ∑ j : Fin 3, (((Finset.range m).filter (fun t => ts t = j)).card : ℝ) * g j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem range_filter_len (p : ℕ → Prop) [DecidablePred p] (m : ℕ) :
    ((List.range m).filter (fun s => decide (p s))).length = ((Finset.range m).filter p).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : p m <;> simp [h]

section CD

variable (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X : Plane} {κ : Type} [Fintype κ]
  (F : ExtFan D.toRegionDissection X κ) (hcor : ∀ x : AtV D.toRegionDissection X, 0 < crs (F.p x) (F.q x))

include hcor

theorem cd_ex (x : AtV D.toRegionDissection X) :
    ∃ p : Fin 3 × Bool, (D.tile x.1).pts p.1 = X ∧ F.p x = toV2 ((D.tile x.1).pts (armP p.1 p.2) - X) ∧
      F.q x = toV2 ((D.tile x.1).pts (armQ p.1 p.2) - X) := by
  obtain ⟨k, hk⟩ := F.corner_of_crs x (hcor x)
  obtain ⟨kk, fl, h1, h2, h3⟩ := spec_corner_data (F.hspec x) ⟨k, hk⟩
  exact ⟨(kk, fl), h1, h2, h3⟩


/-- Canonical corner data of a corner sector. -/
noncomputable def cd (x : AtV D.toRegionDissection X) : Fin 3 × Bool := Classical.choose (cd_ex D F hcor x)


theorem cd_spec (x : AtV D.toRegionDissection X) :
    (D.tile x.1).pts (cd D F hcor x).1 = X ∧ F.p x = toV2 ((D.tile x.1).pts (armP (cd D F hcor x).1 (cd D F hcor x).2) - X) ∧
      F.q x = toV2 ((D.tile x.1).pts (armQ (cd D F hcor x).1 (cd D F hcor x).2) - X) :=
  Classical.choose_spec (cd_ex D F hcor x)


/-- The code of a corner sector. -/
noncomputable def cdcode (x : AtV D.toRegionDissection X) : ℕ := codeOf (idx x.1) (cd D F hcor x).1 (cd D F hcor x).2


theorem cdcode_spec (x : AtV D.toRegionDissection X) :
    RegFan.tT (cdcode D idx F hcor x) = (idx x.1 (cd D F hcor x).1 : ℕ) ∧
    RegFan.tU (cdcode D idx F hcor x) = (idx x.1 (armP (cd D F hcor x).1 (cd D F hcor x).2) : ℕ) ∧
    RegFan.tW (cdcode D idx F hcor x) = (idx x.1 (armQ (cd D F hcor x).1 (cd D F hcor x).2) : ℕ) ∧
    cdcode D idx F hcor x < 6 :=
  codeOf_spec' (idx x.1) _ _


/-- The cyclic list of codes of `m` consecutive sectors from base index `b`. -/
noncomputable def lst (hemp : IsEmpty κ) (b : ℕ) : List ℕ :=
  (List.range (Fintype.card (AtV D.toRegionDissection X))).map (fun s => cdcode D idx F hcor (tl F hemp (b + s)))


theorem lst_length (hemp : IsEmpty κ) (b : ℕ) : (lst D idx F hcor hemp b).length = Fintype.card (AtV D.toRegionDissection X) := by
  simp [lst]


theorem lst_getD (hemp : IsEmpty κ) (b s : ℕ) (hs : s < Fintype.card (AtV D.toRegionDissection X)) :
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
  have := sum_tl F hemp (fun x : AtV D.toRegionDissection X => if (idx x.1 (cd D F hcor x).1 : Fin 3) = j then 1 else 0) b
  rw [← this]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have h := (cdcode_spec D idx F hcor (tl F hemp (b + s))).1
  simp only [h, beq_iff_eq]
  congr 1
  simp [Fin.ext_iff]


/-- Two corner sectors with the same ending ray coincide. -/
theorem corner_end_unique {x y : AtV D.toRegionDissection X} (hx : 0 < crs (F.p x) (F.q x)) (hy : 0 < crs (F.p y) (F.q y))
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
theorem gk_side (x : AtV D.toRegionDissection X) {Z : Plane} {kv kz : Fin 3} (hkv : (D.tile x.1).pts kv = X) (hkz : (D.tile x.1).pts kz = Z)
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
theorem gk_adj (hemp : IsEmpty κ) {Z : Plane} (hE : GkEdge D.toRegionDissection idx Z X) :
    ∃ n : ℕ, idx (tl F hemp n).1 (cd D F hcor (tl F hemp n)).1 = 1 ∧
      idx (tl F hemp n).1 (armQ (cd D F hcor (tl F hemp n)).1 (cd D F hcor (tl F hemp n)).2) = 2 ∧
      idx (tl F hemp (n + 1)).1 (cd D F hcor (tl F hemp (n + 1))).1 = 1 ∧
      idx (tl F hemp (n + 1)).1 (armP (cd D F hcor (tl F hemp (n + 1))).1 (cd D F hcor (tl F hemp (n + 1))).2) = 2 := by
  classical
  obtain ⟨i, j, k1, k2, k1', k2', hij, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hE
  set xi : AtV D.toRegionDissection X := ⟨i, vertex_mem a2⟩
  set xj : AtV D.toRegionDissection X := ⟨j, vertex_mem a4⟩
  have hk12 : k1 ≠ k2 := fun h => by rw [h] at a5; rw [a5] at a6; exact absurd a6 (by decide)
  have hk12' : k1' ≠ k2' := fun h => by rw [h] at a7; rw [a7] at a8; exact absurd a8 (by decide)
  have si := gk_side D idx F hcor xi (kv := k2) (kz := k1) a2 a1 hk12 a6 a5
  have sj := gk_side D idx F hcor xj (kv := k2') (kz := k1') a4 a3 hk12' a8 a7
  -- the common direction `Z - X`
  have hv : toV2 ((D.tile i).pts k1 - X) = toV2 ((D.tile j).pts k1' - X) := by rw [a1, a3]
  have hvi : (D.tile i).pts k1 = (D.tile j).pts k1' := by rw [a1, a3]
  -- consecutive sectors
  have succ_of : ∀ (x y : AtV D.toRegionDissection X), Par (F.p y) (F.q x) → ∃ n, tl F hemp n = x ∧ tl F hemp (n + 1) = y := by
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


theorem wd_cd' (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (x : AtV D.toRegionDissection X) :
    wd (F.p x) (F.q x) = D.model.angleAt (idx x.1 (cd D F hcor x).1) := by
  obtain ⟨hk, -, -⟩ := cd_spec D F hcor x
  have h1 : wd (F.p x) (F.q x) = (D.tile x.1).angleAt (cd D F hcor x).1 := by
    rw [F.hwd x]
    have e := Tri.localAngle_vertex (D.tile x.1) (cd D F hcor x).1
    rw [hk] at e
    have e2 : (D.tile x.1).angleAt (cd D F hcor x).1 =
        cornerAngle ((D.tile x.1).pts ((cd D F hcor x).1 + 1)) X ((D.tile x.1).pts ((cd D F hcor x).1 + 2)) := by
      unfold Tri.angleAt; rw [hk]
    rw [e2]; exact e
  rw [h1, ← hidxA]

theorem opp_colG_aux (hemp : IsEmpty κ) (b i : ℕ) (hi : i < Fintype.card (AtV D.toRegionDissection X)) (s : AtV D.toRegionDissection X)
    (hs : Par (F.p s) (neg2 (F.q (tl F hemp (b + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X)))))) :
    ∃ m' : ℕ, 0 < m' ∧ m' < Fintype.card (AtV D.toRegionDissection X) ∧
      ∑ t ∈ Finset.range m', wd (F.p (tl F hemp (b + i + t))) (F.q (tl F hemp (b + i + t))) = Real.pi := by
  classical
  set m := Fintype.card (AtV D.toRegionDissection X) with hm
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
    have h1 := sum_tl F hemp (fun x : AtV D.toRegionDissection X => wd (F.p x) (F.q x)) c
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
  exact ⟨m', Nat.pos_of_ne_zero hm0, hm', by simpa [hu', hv'] using hπ⟩


/-- **Generic opposite ray ⇒ collinearity flag** (`γ = π/3`, `α + β = 2π/3`, `a` not a rational combination of `b, c`, a complete fan of type `(3,3,0)` or `(2,2,2)`):
if some sector starts along the direction opposite to ray `i`, a block of consecutive corners from ray `i` has type counts `(1,1,1)` or `(0,0,3)`. -/
theorem opp_colG (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hγ : D.model.angleAt 2 = Real.pi / 3)
    (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = 2 * Real.pi / 3)
    (hprof : (cnt D idx X 0 = 3 ∧ cnt D idx X 1 = 3 ∧ cnt D idx X 2 = 0) ∨ (cnt D idx X 0 = 2 ∧ cnt D idx X 1 = 2 ∧ cnt D idx X 2 = 2))
    (hemp : IsEmpty κ) (b i : ℕ) (hi : i < Fintype.card (AtV D.toRegionDissection X)) (s : AtV D.toRegionDissection X)
    (hs : Par (F.p s) (neg2 (F.q (tl F hemp (b + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X)))))) :
    RegFan.colG (lst D idx F hcor hemp b) i = true := by
  classical
  obtain ⟨m', hm0, hm', hπ⟩ := opp_colG_aux D F hcor hemp b i hi s hs
  set m := Fintype.card (AtV D.toRegionDissection X) with hm
  have hpos : 0 < m := card_pos_atV F hemp
  set c := b + i with hc
  let typ : ℕ → Fin 3 := fun t => idx (tl F hemp (c + t)).1 (cd D F hcor (tl F hemp (c + t))).1
  have hwdt : ∀ t, wd (F.p (tl F hemp (c + t))) (F.q (tl F hemp (c + t))) = D.model.angleAt (typ t) :=
    fun t => wd_cd' D idx F hcor hidxA _
  have hlen := lst_length D idx F hcor hemp b
  have hkey : ∀ t, RegFan.tT ((lst D idx F hcor hemp b).getD ((i + t) % (lst D idx F hcor hemp b).length) 0) = (typ t : ℕ) := by
    intro t
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
  have hblk : ∀ j : Fin 3, RegFan.blk (lst D idx F hcor hemp b) i m' (j : ℕ) = ((Finset.range m').filter (fun t => typ t = j)).card := by
    intro j
    unfold RegFan.blk
    rw [← range_filter_len (fun t => typ t = j)]
    congr 1
    apply List.filter_congr
    intro t _
    rw [hkey t, Bool.eq_iff_iff]
    simp [Fin.ext_iff]
  have hbnd : ∀ j : Fin 3, ((Finset.range m').filter (fun t => typ t = j)).card ≤ cnt D idx X j := by
    intro j
    rw [cnt_atv D idx (fun x => (cd D F hcor x).1) (fun x => (cd_spec D F hcor x).1) j]
    refine Finset.card_le_card_of_injOn (fun t => tl F hemp (c + t)) ?_ ?_
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact ht.2
    · intro t ht t' ht' h
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ht ht'
      have h1 := tl_inj_mod F hemp h
      have h2 : (c + t) ≡ (c + t') [MOD m] := h1
      have h3 := Nat.ModEq.add_left_cancel' c h2
      exact Nat.ModEq.eq_of_lt_of_lt h3 (lt_trans ht.1 hm') (lt_trans ht'.1 hm')
  set n0 := ((Finset.range m').filter (fun t => typ t = 0)).card with hn0
  set n1 := ((Finset.range m').filter (fun t => typ t = 1)).card with hn1
  set n2 := ((Finset.range m').filter (fun t => typ t = 2)).card with hn2
  have hsum : (n0 : ℝ) * D.model.angleAt 0 + n1 * D.model.angleAt 1 + n2 * D.model.angleAt 2 = Real.pi := by
    have h1 : ∑ t ∈ Finset.range m', wd (F.p (tl F hemp (c + t))) (F.q (tl F hemp (c + t))) =
        ∑ t ∈ Finset.range m', D.model.angleAt (typ t) := Finset.sum_congr rfl (fun t _ => hwdt t)
    have h2 := sum_by_type m' typ D.model.angleAt
    rw [Fin.sum_univ_three] at h2
    rw [← hπ, h1, h2]
  have hb : (n2 = 0 ∧ n0 ≤ 3 ∧ n1 ≤ 3) ∨ (n0 ≤ 2 ∧ n1 ≤ 2 ∧ n2 ≤ 2) := by
    have b0 := hbnd 0
    have b1 := hbnd 1
    have b2 := hbnd 2
    rcases hprof with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · left; refine ⟨?_, ?_, ?_⟩ <;> omega
    · right; refine ⟨?_, ?_, ?_⟩ <;> omega
  have heq := block_eq D hnc hγ hαβ n0 n1 n2 hb hsum
  have h2c : 2 * n0 + n2 = 3 := by
    have h' : (n0 : ℝ) * (2 * Real.pi / 3) + n2 * (Real.pi / 3) = Real.pi := by
      rw [hγ] at hsum
      have : (n1 : ℝ) = n0 := by exact_mod_cast heq.symm
      rw [this] at hsum
      nlinarith [hsum, hαβ]
    have hp := Real.pi_pos
    have : ((2 * n0 + n2 : ℕ) : ℝ) = 3 := by
      push_cast
      have : ((2 : ℝ) * n0 + n2) * (Real.pi / 3) = 3 * (Real.pi / 3) := by nlinarith [h']
      exact mul_right_cancel₀ (by positivity) this
    exact_mod_cast this
  unfold RegFan.colG
  rw [List.any_eq_true]
  refine ⟨m', List.mem_range.mpr (by rw [hlen]; exact hm'), ?_⟩
  have e0 := hblk 0
  have e1 := hblk 1
  have e2 := hblk 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
  rw [e0, e1, e2]
  have : (n0 = 0 ∧ n2 = 3) ∨ (n0 = 1 ∧ n2 = 1) := by omega
  rcases this with ⟨a0, a2⟩ | ⟨a0, a2⟩
  · simp [← hn0, ← hn1, ← hn2, a0, a2, ← heq]
  · simp [← hn0, ← hn1, ← hn2, a0, a2, ← heq]

end CD

end Erdos634.Draft.LaczFormal.RG
