-- Draft/FluxFRow14F4.lean — ROW 14, F4 (Beeson III Lemma 5, `rationality_proofs.md` §0 F4) for a
-- REAL `CongruentDissection`: on row 14's target `(2α, β, α+β)`, the side joining the `2α` and
-- `α+β` corners (side `Y`, opposite the single-tile `β` corner) carries a `c`-edge, and its real
-- chain gives a word `dist = P·a + Q·b + R·c` with `R ≥ 1`.
--
-- REDISCOVERY / REUSE, stated plainly: the junction-counting argument that `FluxFRow14Derive.lean`
-- (and EVIDENCE P64/P82) recorded as "NOT built" already existed in the corpus since 2026-09-10 as
-- `GammaTrap.congruentDissection_gammatrap` (base-β sides). Its only corner-specific input is
-- `congruentDissection_endpoints_of_chain` (no γ at the two ends of the side). The first theorem
-- below is that proof, copied verbatim with that one input replaced by the hypotheses
-- `hA0`/`hA1` ("no tile presents γ at either end of the side"); the second copies
-- `SideWalk.equal_side_no_b_of_gammatrap`'s walk-equation derivation. New content is only the
-- relation-generic restatement and the row-14 instantiation (`row14_F4`, `row14_side_word`), whose
-- corner hypotheses are discharged from `FluxFRow14Bridge`'s real corner counts.
--
-- Formalization debt (paper-level PROVED); not progress on the three /goal outcomes.
import Erdos634.GammaTrap
import Erdos634.SideWalk
import Erdos634.Draft.FluxFRow14Bridge

namespace Erdos634.Row14F4

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.TilePlacement
open Erdos634.WallEndpoints Erdos634.Placement Erdos634.BaseChain
open Erdos634.ChainInstance Erdos634.OrientBridge
open Erdos634.GammaCascade Erdos634.SideWall Erdos634.Row14Bridge

variable {N : ℕ}

/-- **F4, relation-generic.**  For the `3α+2β = π`, `γ = 2α+β` tile (`α ∉ ℚπ`), any side `k` of
the target at whose two ends no tile presents `γ` carries a `c`-edge. -/
theorem gammatrap_of_no_corner_gamma (hN : 0 < N) (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3) (dir : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ v : Plane, (wallFun D.target k).linear v = 0 → dir v = 0 → v = 0)
    (hdirab : dir (D.target.pts k) ≤ dir (D.target.pts (k + 1)))
    (hthird : ∀ p ∈ wallList D.toDissection (wallFun D.target k) 0,
      wallFun D.target k ((D.tile p.1).pts (p.2 + 2)) < 0)
    (hA0 : ∀ i : Fin N, (D.tile i).localAngle (D.target.pts k) ≠ γ)
    (hA1 : ∀ i : Fin N, (D.tile i).localAngle (D.target.pts (k + 1)) ≠ γ) :
    ∃ p ∈ wallList D.toDissection (wallFun D.target k) 0,
      dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1)) = sideOpp D.model 2 := by
  classical
  by_contra hcon
  push_neg at hcon
  set g := wallFun D.target k with hgdef
  set n := (wallList D.toDissection g 0).length with hndef
  have hab : D.target.pts k ≠ D.target.pts (k + 1) := by
    have h : ∀ x : Fin 3, x ≠ x + 1 := by decide
    exact Erdos634.TilePlacement.pts_ne D.target (h k)
  have hwall : ∀ y ∈ D.target.carrier, g y ≤ 0 := fun y hy => wallFun_le D.target k hy
  have hbase : segment ℝ (D.target.pts k) (D.target.pts (k+1)) ⊆ frontier D.target.carrier := by
    intro y hy
    exact edge_subset_frontier D.target k (by rw [Tri.edge]; exact hy)
  have hline : ∀ y ∈ segment ℝ (D.target.pts k) (D.target.pts (k+1)), g y = 0 := by
    intro y hy
    exact wallFun_eq_zero D.target k (by rw [Tri.edge]; exact hy)
  have hface : ∀ y ∈ D.target.carrier, g y = 0 →
      y ∈ segment ℝ (D.target.pts k) (D.target.pts (k+1)) := by
    intro y hy h0
    have := wallFun_face D.target k hy h0
    rw [Tri.edge] at this
    exact this
  obtain ⟨E, n2, hneq, hn0, hwest, heast, hinternal, hmem, hEinj, hstrictlo, hstricthi, hnondeg, _hsurj⟩ :=
    chain_endpoints hN D.toDissection g 0 dir hker hwall (D.target.pts k) (D.target.pts (k+1))
      hab hdirab hbase hline hface hthird
  rw [← hndef] at hneq
  subst hneq
  -- every edge is `a` or `b` (its length is not the model's `c`-side)
  have hnoc : ∀ m, m < n →
      dist ((D.tile (E m).1).pts (E m).2) ((D.tile (E m).1).pts ((E m).2 + 1)) ≠ sideOpp D.model 2 :=
    fun m hm heq => hcon (E m) (hmem m hm) heq
  have hgamma : ∀ m, m < n →
      (angleAt (D.tile (E m).1) (E m).2 = γ ∧ angleAt (D.tile (E m).1) ((E m).2 + 1) ≠ γ) ∨
      (angleAt (D.tile (E m).1) ((E m).2 + 1) = γ ∧ angleAt (D.tile (E m).1) (E m).2 ≠ γ) := by
    intro m hm
    obtain ⟨j, hj⟩ := exists_matching_side D (E m).1 (E m).2
    refine gamma_at_one_endpoint D α β γ hα' hβ' hγ' hscalene hαγ hβγ (E m).1 (E m).2 j ?_ hj
    intro h2; rw [h2] at hj; exact hnoc m hm hj
  have hgamma' : ∀ m, m < n →
      ((D.tile (E m).1).localAngle (edgeWest D.toDissection dir (E m)) = γ ∧
          (D.tile (E m).1).localAngle (edgeEast D.toDissection dir (E m)) ≠ γ) ∨
      ((D.tile (E m).1).localAngle (edgeEast D.toDissection dir (E m)) = γ ∧
          (D.tile (E m).1).localAngle (edgeWest D.toDissection dir (E m)) ≠ γ) := by
    intro m hm
    rcases localAngle_edgeWest_edgeEast D.toDissection dir (E m).1 (E m).2 with ⟨hW, hE⟩ | ⟨hW, hE⟩
    · rcases hgamma m hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [hW, hE]; exact ⟨h1, h2⟩
      · right; rw [hW, hE]; exact ⟨h1, h2⟩
    · rcases hgamma m hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; rw [hW, hE]; exact ⟨h1, h2⟩
      · left; rw [hW, hE]; exact ⟨h1, h2⟩
  -- `place`, matching `cascade`'s 1-indexed convention: edge `i` (cascade) is `E (i-1)` (ours)
  set place : ℕ → ℕ := fun i =>
    if (D.tile (E (i - 1)).1).localAngle (edgeWest D.toDissection dir (E (i - 1))) = γ
      then i - 1 else i with hplace_def
  have hplace : ∀ i, 1 ≤ i → i ≤ n → place i = i - 1 ∨ place i = i := by
    intro i _ _; simp only [hplace_def]; split
    · left; rfl
    · right; rfl
  have hplace_west : ∀ i, (D.tile (E (i - 1)).1).localAngle
      (edgeWest D.toDissection dir (E (i - 1))) = γ → place i = i - 1 := by
    intro i hW; simp only [hplace_def, if_pos hW]
  have hplace_east : ∀ i, (D.tile (E (i - 1)).1).localAngle
      (edgeWest D.toDissection dir (E (i - 1))) ≠ γ → place i = i := by
    intro i hW; simp only [hplace_def, if_neg hW]
  -- `hends`
  have hends : ∀ i, 1 ≤ i → i ≤ n → place i ≠ 0 ∧ place i ≠ n := by
    intro i hi1 hin
    rcases hplace i hi1 hin with hpe | hpe
    · refine ⟨?_, by omega⟩
      intro h0
      have hi1eq : i = 1 := by omega
      subst hi1eq
      have hW : (D.tile (E 0).1).localAngle (edgeWest D.toDissection dir (E 0)) = γ := by
        by_contra hne
        have := hplace_east 1 hne
        simp at this; omega
      rw [hwest] at hW
      exact hA0 _ hW
    · refine ⟨by omega, ?_⟩
      intro hn'
      have hieq : i = n := by omega
      subst hieq
      have hWn : ¬ (D.tile (E (n - 1)).1).localAngle
          (edgeWest D.toDissection dir (E (n - 1))) = γ := by
        intro hcontra
        have := hplace_west n hcontra
        omega
      have hEn : (D.tile (E (n - 1)).1).localAngle
          (edgeEast D.toDissection dir (E (n - 1))) = γ := by
        rcases hgamma' (n - 1) (by omega) with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd h1 hWn
        · exact h1
      rw [heast] at hEn
      exact hA1 _ hEn
  -- `hinj`: reduces to consecutive indices sharing one junction
  have hinj : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i ≠ j → place i ≠ place j := by
    intro i j hi1 hin hj1 hjn hij heq
    wlog hlt : i < j generalizing i j
    · exact this j i hj1 hjn hi1 hin hij.symm heq.symm (by omega)
    have hpi0 := hplace i hi1 hin
    have hpj0 := hplace j hj1 hjn
    have hjeq : j = i + 1 := by rcases hpi0 with hpi0 | hpi0 <;> rcases hpj0 with hpj0 | hpj0 <;> omega
    subst hjeq
    have hji : place i = i ∧ place (i + 1) = i := by
      rcases hpi0 with hpi0 | hpi0 <;> rcases hpj0 with hpj0 | hpj0 <;> omega
    have hWi_east : (D.tile (E (i - 1)).1).localAngle
        (edgeEast D.toDissection dir (E (i - 1))) = γ := by
      rcases hgamma' (i - 1) (by omega) with ⟨h1, _⟩ | ⟨h1, _⟩
      · have := hplace_west i h1
        omega
      · exact h1
    have hWi1_west : (D.tile (E i).1).localAngle
        (edgeWest D.toDissection dir (E i)) = γ := by
      by_contra hne
      have := hplace_east (i + 1) hne
      omega
    have hshared : edgeEast D.toDissection dir (E (i - 1)) = edgeWest D.toDissection dir (E i) := by
      have := hinternal (i - 1) (show i - 1 + 1 < n by omega)
      rwa [show i - 1 + 1 = i by omega] at this
    have hwi := (mem_wallList D.toDissection g 0 (E (i - 1))).mp (hmem (i - 1) (by omega))
    have hwi1 := (mem_wallList D.toDissection g 0 (E i)).mp (hmem i (by omega))
    have htne : (E (i - 1)).1 ≠ (E i).1 := by
      intro h
      have hne0 : E (i - 1) ≠ E i := fun h' => by
        have := hEinj (i - 1) i (by omega) (by omega) h'; omega
      exact WallSide.wall_edges_same_tile D.toDissection g 0
        ⟨(D.tile (E (i-1)).1).pts ((E (i-1)).2 + 2),
          ne_of_lt (hthird (E (i-1)) (hmem (i-1) (by omega)))⟩
        (E (i - 1)) (E i) hne0 h hwi hwi1
    -- the shared point is an interior frontier non-vertex point
    set v := edgeEast D.toDissection dir (E (i - 1)) with hvdef
    have hvtile : v ∈ (D.tile (E (i-1)).1).carrier := by
      rw [hvdef, Placement.edgeEast]
      split <;> exact subset_convexHull ℝ _ (Set.mem_range_self _)
    have hp : v ∈ D.target.carrier := Erdos634.BaseSelection.tile_subset_target
      D.toDissection (E (i-1)).1 hvtile
    have hgp : g v = 0 := (Erdos634.BridgeC.g_ends D.toDissection g 0 dir (E (i-1)) hwi).2
    have hdv : dir v = edgeEnd D.toDissection dir (E (i-1)) := (dir_edgeEast D.toDissection dir
      (E (i-1)))
    have hstrict1 : dir (D.target.pts k) < dir v := by
      rw [hdv]
      rcases Nat.eq_zero_or_pos (i - 1) with h0 | hpos
      · have hposi : edgePos D.toDissection dir (E (i-1)) < edgeEnd D.toDissection dir (E (i-1)) :=
          hnondeg (i-1) (by omega)
        have heqpos : edgePos D.toDissection dir (E (i-1)) = dir (D.target.pts k) := by
          rw [h0] at hposi ⊢
          rw [← dir_edgeWest D.toDissection dir (E 0), hwest]
        linarith [hposi, heqpos]
      · calc dir (D.target.pts k) < edgePos D.toDissection dir (E (i-1)) := hstrictlo (i-1) hpos (by omega)
          _ < edgeEnd D.toDissection dir (E (i-1)) := hnondeg (i-1) (by omega)
    have hstrict2 : dir v < dir (D.target.pts (k+1)) := by
      rw [hdv]; exact hstricthi (i-1) (by omega)
    have hnv := side_junction_frontier_nonvertex D.toDissection k dir hp hgp
      ⟨lt_of_le_of_lt (min_le_left _ _) hstrict1, lt_of_lt_of_le hstrict2 (le_max_right _ _)⟩
    have hWi1_west' : (D.tile (E i).1).localAngle v = γ := by
      rw [hshared]; exact hWi1_west
    exact congruentDissection_no_double_gamma D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
      hγdef hrel hirr hα' hβ' hγ' hnv.1 hnv.2 (E (i-1)).1 (E i).1 htne hWi_east hWi1_west'
  -- assemble `cascade`
  -- assemble `cascade`
  exact cascade n hn0 place hplace hinj hends


/-- **The side's real walk equation with a `c`-edge.**  Under the hypotheses of
`gammatrap_of_no_corner_gamma` plus the calibration `hiso` (as in `SideWalk.side_walk_of_dissection`),
the side's length is `P·a + Q·b + R·c` with `P, Q, R` the real edge-type counts of its chain and
`R ≥ 1`. -/
theorem side_word_of_no_corner_gamma (hN : 0 < N) (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hscalenef : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3) (dir : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ v : Plane, (wallFun D.target k).linear v = 0 → dir v = 0 → v = 0)
    (hdirab : dir (D.target.pts k) ≤ dir (D.target.pts (k + 1)))
    (hthird : ∀ p ∈ wallList D.toDissection (wallFun D.target k) 0,
      wallFun D.target k ((D.tile p.1).pts (p.2 + 2)) < 0)
    (hA0 : ∀ i : Fin N, (D.tile i).localAngle (D.target.pts k) ≠ γ)
    (hA1 : ∀ i : Fin N, (D.tile i).localAngle (D.target.pts (k + 1)) ≠ γ)
    (hiso : ∀ p q : Plane, (wallFun D.target k) p = 0 → (wallFun D.target k) q = 0 →
      dist p q = |dir p - dir q|) :
    ∃ Pc Qc Rc : ℕ, 1 ≤ Rc ∧
      dist (D.target.pts k) (D.target.pts (k + 1))
        = Pc * sideOpp D.model 0 + Qc * sideOpp D.model 1 + Rc * sideOpp D.model 2 := by
  classical
  set g := wallFun D.target k with hgdef
  set a := D.target.pts k with hadef
  set b := D.target.pts (k + 1) with hbdef
  have hab : a ≠ b := by
    have h : ∀ x : Fin 3, x ≠ x + 1 := by decide
    exact Erdos634.TilePlacement.pts_ne D.target (h k)
  have hwall : ∀ y ∈ D.target.carrier, g y ≤ 0 := fun y hy => wallFun_le D.target k hy
  have hbase : segment ℝ a b ⊆ frontier D.target.carrier := by
    intro y hy
    exact edge_subset_frontier D.target k (by rw [Tri.edge]; exact hy)
  have hline : ∀ y ∈ segment ℝ a b, g y = 0 := by
    intro y hy
    exact wallFun_eq_zero D.target k (by rw [Tri.edge]; exact hy)
  have hface : ∀ y ∈ D.target.carrier, g y = 0 → y ∈ segment ℝ a b := by
    intro y hy h0
    have := wallFun_face D.target k hy h0
    rw [Tri.edge] at this
    exact this
  obtain ⟨pc, hpcmem, hpceq⟩ := gammatrap_of_no_corner_gamma hN D α β γ hαβ hαγ hαπ hα0 hβγ hβπ
    hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hscalenef hα' hβ' hγ' k dir hker hdirab hthird hA0 hA1
  obtain ⟨E, n, hneq, hn0, hwest0, heastlast, hjunc, hmem, hinj, hlba, hlbend, hnondeg, hsurj⟩ :=
    chain_endpoints hN D.toDissection g 0 dir hker hwall a b hab hdirab hbase hline hface hthird
  set L : ℕ → ℝ := fun m => Erdos634.OrientBridge.edgePos D.toDissection dir (E m) with hLdef
  set R : ℕ → ℝ := fun m => Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m) with hRdef
  have hdistm : ∀ m, m < n →
      dist ((D.tile (E m).1).pts (E m).2) ((D.tile (E m).1).pts ((E m).2 + 1)) = R m - L m := by
    intro m hm
    have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g 0 (E m)).mp (hmem m hm)
    rw [hiso _ _ hwm.1 hwm.2]
    show |dir ((D.tile (E m).1).pts (E m).2) - dir ((D.tile (E m).1).pts ((E m).2 + 1))|
      = Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m)
        - Erdos634.OrientBridge.edgePos D.toDissection dir (E m)
    rw [show Erdos634.OrientBridge.edgePos D.toDissection dir (E m)
          = min (dir ((D.tile (E m).1).pts (E m).2)) (dir ((D.tile (E m).1).pts ((E m).2 + 1)))
        from rfl,
      show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m)
          = max (dir ((D.tile (E m).1).pts (E m).2)) (dir ((D.tile (E m).1).pts ((E m).2 + 1)))
        from rfl]
    rcases le_total (dir ((D.tile (E m).1).pts (E m).2))
        (dir ((D.tile (E m).1).pts ((E m).2 + 1))) with h | h
    · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
  have hRL : ∀ m, m < n → R m - L m = sideOpp D.model 0 ∨ R m - L m = sideOpp D.model 1 ∨
      R m - L m = sideOpp D.model 2 := by
    intro m hm
    obtain ⟨j, hj⟩ := exists_matching_side D (E m).1 (E m).2
    rw [← hdistm m hm, hj]
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hscalene : sideOpp D.model 0 ≠ sideOpp D.model 1 ∧ sideOpp D.model 0 ≠ sideOpp D.model 2 ∧
      sideOpp D.model 1 ≠ sideOpp D.model 2 :=
    ⟨hscalenef 0 1 (by decide), hscalenef 0 2 (by decide), hscalenef 1 2 (by decide)⟩
  have hchain := Erdos634.ChainWalk.chain_walk n hn0 L R (sideOpp D.model 0) (sideOpp D.model 1)
    (sideOpp D.model 2) hscalene.1 hscalene.2.1 hscalene.2.2
    (fun j hj => by
      show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E j)
        = Erdos634.OrientBridge.edgePos D.toDissection dir (E (j + 1))
      rw [← dir_edgeEast, ← dir_edgeWest, hjunc j hj])
    (fun m hm => by
      rw [Finset.mem_range] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hRL m hm)
  refine ⟨((Finset.range n).filter (fun j => R j - L j = sideOpp D.model 0)).card,
    ((Finset.range n).filter (fun j => R j - L j = sideOpp D.model 1)).card,
    ((Finset.range n).filter (fun j => R j - L j = sideOpp D.model 2)).card, ?_, ?_⟩
  · obtain ⟨ic, hiclt, hiceq⟩ := hsurj pc hpcmem
    subst hiceq
    apply Erdos634.ChainWalk.count_pos n (fun j => R j - L j) (sideOpp D.model 2) ic
      (Finset.mem_range.mpr hiclt)
    show R ic - L ic = sideOpp D.model 2
    rw [← hdistm ic hiclt, hpceq]
  · have hRb : R (n - 1) = dir b := by
      show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E (n - 1)) = dir b
      rw [← dir_edgeEast, heastlast]
    have hL0 : L 0 = dir a := by
      show Erdos634.OrientBridge.edgePos D.toDissection dir (E 0) = dir a
      rw [← dir_edgeWest, hwest0]
    rw [hiso a b (hline a (left_mem_segment ℝ a b)) (hline b (right_mem_segment ℝ a b))]
    rw [abs_of_nonpos (by linarith)]
    rw [← hchain, hRb, hL0]
    ring

/-- No tile presents `γ` at a `2α` or `α+β` corner of the target (row 14's real corner counts). -/
theorem row14_corner_no_gamma (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 2 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α + β) :
    ∀ i : Fin N, (D.tile i).localAngle (D.target.pts k) ≠ γ := by
  classical
  intro i hi
  have hcard : ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 := by
    rcases hcorner with h | h
    · exact (congruentDissection_row14_2alpha_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0
        hπ0 hγdef hrel hirr hα' hβ' hγ' k h).2.2.1
    · exact (congruentDissection_row14_alphabeta_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ
        hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' k h).2.2.1
  have hmem : i ∈ ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
  rw [Finset.card_eq_zero.mp hcard] at hmem
  simp at hmem

/-- **Row 14's F4 for a real dissection**, with the side's own real word: on the side `k → k+1`
joining the `2α` and `α+β` corners (either order), the chain's word has `R ≥ 1`. -/
theorem row14_side_word (hN : 0 < N) (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hscalenef : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3) (dir : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ v : Plane, (wallFun D.target k).linear v = 0 → dir v = 0 → v = 0)
    (hdirab : dir (D.target.pts k) ≤ dir (D.target.pts (k + 1)))
    (hthird : ∀ p ∈ wallList D.toDissection (wallFun D.target k) 0,
      wallFun D.target k ((D.tile p.1).pts (p.2 + 2)) < 0)
    (hc0 : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 2 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α + β)
    (hc1 : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1)) (D.target.pts (k + 1 + 2))
        = 2 * α ∨
      cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1)) (D.target.pts (k + 1 + 2))
        = α + β)
    (hiso : ∀ p q : Plane, (wallFun D.target k) p = 0 → (wallFun D.target k) q = 0 →
      dist p q = |dir p - dir q|) :
    ∃ Pc Qc Rc : ℕ, 1 ≤ Rc ∧
      dist (D.target.pts k) (D.target.pts (k + 1))
        = Pc * sideOpp D.model 0 + Qc * sideOpp D.model 1 + Rc * sideOpp D.model 2 :=
  side_word_of_no_corner_gamma hN D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr
    hscalenef hα' hβ' hγ' k dir hker hdirab hthird
    (row14_corner_no_gamma D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr
      hα' hβ' hγ' k hc0)
    (row14_corner_no_gamma D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr
      hα' hβ' hγ' (k + 1) hc1)
    hiso

end Erdos634.Row14F4

#print axioms Erdos634.Row14F4.gammatrap_of_no_corner_gamma
#print axioms Erdos634.Row14F4.side_word_of_no_corner_gamma
#print axioms Erdos634.Row14F4.row14_corner_no_gamma
#print axioms Erdos634.Row14F4.row14_side_word
