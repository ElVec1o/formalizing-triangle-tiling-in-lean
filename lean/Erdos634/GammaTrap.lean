import Erdos634.TileAt
import Erdos634.EdgeType
import Erdos634.GammaCascade
import Erdos634.SideWall

/-!
# `prop:gammatrap`, assembled: every side of a base-β target carries a `c`-edge

Erdős #634. The two hard geometric inputs `GammaCascade.cascade` needs are real theorems
(`gamma_at_one_endpoint`, `congruentDissection_no_double_gamma`); this file does the remaining
assembly against a real side's chain (`SideWall.side_chain_junctions`'s wall functional,
`k`/`k+1` convention).

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Geometry.Dissection

open Erdos634.TilePlacement Erdos634.WallEndpoints Erdos634.Placement Erdos634.BaseChain
open Erdos634.ChainInstance Erdos634.OrientBridge
open Erdos634.GammaCascade Erdos634.SideWall

variable {N : ℕ}

/-- **`prop:gammatrap`, for a real `CongruentDissection`.**  Every side carries at least one
`c`-edge. -/
theorem congruentDissection_gammatrap (hN : 0 < N) (D : CongruentDissection N) (α β γ : ℝ)
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
    (hcornerbase : cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) = β)
    (hcornerapex : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = 3 * α) :
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
  obtain ⟨hbβ, hbα⟩ := congruentDissection_endpoints_of_chain D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' k (k + 1) dir hcornerbase hcornerapex E n hwest heast
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
      exact hβγ (hW ▸ hbβ).symm
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
      exact hαγ (hEn ▸ hbα).symm
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


/-- **`prop:gammatrap`, for the base (β→β) side.** If both endpoint corners carry angle β,
the side carries at least one `c`-edge.  Together with `congruentDissection_gammatrap`
(β→3α leg), this covers all three sides of a base-β target (the apex-to-β leg follows
by flipping the direction linear functional). -/
theorem congruentDissection_gammatrap_base (hN : 0 < N) (D : CongruentDissection N) (α β γ : ℝ)
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
    (hcornerbase : cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) = β)
    (hcornerapex : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = β) :
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
  -- start endpoint: tile presents β (corner angle = β)
  have hbβ : (D.tile (E 0).1).localAngle (D.target.pts k) = β := by
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, D.target.pts k = (D.tile (E 0).1).pts j := by
      unfold edgeWest at hwest
      split at hwest
      · exact ⟨(E 0).2, hwest.symm⟩
      · exact ⟨(E 0).2 + 1, hwest.symm⟩
    have hval : (D.tile (E 0).1).localAngle (D.target.pts k)
        = cornerAngle ((D.tile (E 0).1).pts (j + 1)) ((D.tile (E 0).1).pts j)
          ((D.tile (E 0).1).pts (j + 2)) := by rw [hj, Tri.localAngle_vertex]
    obtain ⟨m, hm⟩ := congruent_corner_angles (D.tiles_congruent (E 0).1).symm j
    rw [hval, hm]
    have h := congruentDissection_base_corner_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
      hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' k hcornerbase
    have hcard : ({i | (D.tile i).localAngle (D.target.pts k)
        = cornerAngle (D.model.pts (m + 1)) (D.model.pts m) (D.model.pts (m + 2))} :
        Finset (Fin N)).card ≠ 0 := by
      refine Finset.card_ne_zero_of_mem (a := (E 0).1) ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [hval, hm]
    fin_cases m
    · exact absurd (show cornerAngle (D.model.pts (0 + 1)) (D.model.pts 0)
        (D.model.pts (0 + 2)) = α from hα') (fun heq => hcard (heq ▸ h.1))
    · exact hβ'
    · exact absurd (show cornerAngle (D.model.pts (2 + 1)) (D.model.pts 2)
        (D.model.pts (2 + 2)) = γ from hγ') (fun heq => hcard (heq ▸ h.2.2.1))
  -- end endpoint: tile also presents β (corner angle = β, using base_corner_counts)
  have hbβ2 : (D.tile (E (n - 1)).1).localAngle (D.target.pts (k + 1)) = β := by
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, D.target.pts (k + 1) = (D.tile (E (n - 1)).1).pts j := by
      unfold edgeEast at heast
      split at heast
      · exact ⟨(E (n - 1)).2 + 1, heast.symm⟩
      · exact ⟨(E (n - 1)).2, heast.symm⟩
    have hval : (D.tile (E (n - 1)).1).localAngle (D.target.pts (k + 1))
        = cornerAngle ((D.tile (E (n - 1)).1).pts (j + 1)) ((D.tile (E (n - 1)).1).pts j)
          ((D.tile (E (n - 1)).1).pts (j + 2)) := by rw [hj, Tri.localAngle_vertex]
    obtain ⟨m, hm⟩ := congruent_corner_angles (D.tiles_congruent (E (n - 1)).1).symm j
    rw [hval, hm]
    have h := congruentDissection_base_corner_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
      hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' (k + 1) hcornerapex
    have hcard : ({i | (D.tile i).localAngle (D.target.pts (k + 1))
        = cornerAngle (D.model.pts (m + 1)) (D.model.pts m) (D.model.pts (m + 2))} :
        Finset (Fin N)).card ≠ 0 := by
      refine Finset.card_ne_zero_of_mem (a := (E (n - 1)).1) ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [hval, hm]
    fin_cases m
    · exact absurd (show cornerAngle (D.model.pts (0 + 1)) (D.model.pts 0)
        (D.model.pts (0 + 2)) = α from hα') (fun heq => hcard (heq ▸ h.1))
    · exact hβ'
    · exact absurd (show cornerAngle (D.model.pts (2 + 1)) (D.model.pts 2)
        (D.model.pts (2 + 2)) = γ from hγ') (fun heq => hcard (heq ▸ h.2.2.1))
  -- cascade body: identical to congruentDissection_gammatrap except the apex uses hβγ not hαγ
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
      exact hβγ (hW ▸ hbβ).symm
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
      exact hβγ (hEn ▸ hbβ2).symm  -- β at end, not α
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
  exact cascade n hn0 place hplace hinj hends


/-- **`prop:gammatrap`, for the apex-to-β leg.** If the start corner carries 3α and the
end corner carries β, the side carries at least one `c`-edge.  Together with
`congruentDissection_gammatrap` (β→3α) and `congruentDissection_gammatrap_base` (β→β),
this completes the three-side coverage of `prop:gammatrap`. -/
theorem congruentDissection_gammatrap_apexstart (hN : 0 < N) (D : CongruentDissection N) (α β γ : ℝ)
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
    (hcornerbase : cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) = 3 * α)
    (hcornerapex : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = β) :
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
  -- start endpoint: tile presents α (corner angle = 3α, apex)
  have hbα : (D.tile (E 0).1).localAngle (D.target.pts k) = α := by
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, D.target.pts k = (D.tile (E 0).1).pts j := by
      unfold edgeWest at hwest
      split at hwest
      · exact ⟨(E 0).2, hwest.symm⟩
      · exact ⟨(E 0).2 + 1, hwest.symm⟩
    have hval : (D.tile (E 0).1).localAngle (D.target.pts k)
        = cornerAngle ((D.tile (E 0).1).pts (j + 1)) ((D.tile (E 0).1).pts j)
          ((D.tile (E 0).1).pts (j + 2)) := by rw [hj, Tri.localAngle_vertex]
    obtain ⟨m, hm⟩ := congruent_corner_angles (D.tiles_congruent (E 0).1).symm j
    rw [hval, hm]
    have h := congruentDissection_apex_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
      hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' k hcornerbase
    have hcard : ({i | (D.tile i).localAngle (D.target.pts k)
        = cornerAngle (D.model.pts (m + 1)) (D.model.pts m) (D.model.pts (m + 2))} :
        Finset (Fin N)).card ≠ 0 := by
      refine Finset.card_ne_zero_of_mem (a := (E 0).1) ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [hval, hm]
    fin_cases m
    · exact hα'
    · exact absurd (show cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1)
        (D.model.pts (1 + 2)) = β from hβ') (fun heq => hcard (heq ▸ h.2.1))
    · exact absurd (show cornerAngle (D.model.pts (2 + 1)) (D.model.pts 2)
        (D.model.pts (2 + 2)) = γ from hγ') (fun heq => hcard (heq ▸ h.2.2.1))
  -- end endpoint: tile presents β (corner angle = β)
  have hbβ : (D.tile (E (n - 1)).1).localAngle (D.target.pts (k + 1)) = β := by
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, D.target.pts (k + 1) = (D.tile (E (n - 1)).1).pts j := by
      unfold edgeEast at heast
      split at heast
      · exact ⟨(E (n - 1)).2 + 1, heast.symm⟩
      · exact ⟨(E (n - 1)).2, heast.symm⟩
    have hval : (D.tile (E (n - 1)).1).localAngle (D.target.pts (k + 1))
        = cornerAngle ((D.tile (E (n - 1)).1).pts (j + 1)) ((D.tile (E (n - 1)).1).pts j)
          ((D.tile (E (n - 1)).1).pts (j + 2)) := by rw [hj, Tri.localAngle_vertex]
    obtain ⟨m, hm⟩ := congruent_corner_angles (D.tiles_congruent (E (n - 1)).1).symm j
    rw [hval, hm]
    have h := congruentDissection_base_corner_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
      hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' (k + 1) hcornerapex
    have hcard : ({i | (D.tile i).localAngle (D.target.pts (k + 1))
        = cornerAngle (D.model.pts (m + 1)) (D.model.pts m) (D.model.pts (m + 2))} :
        Finset (Fin N)).card ≠ 0 := by
      refine Finset.card_ne_zero_of_mem (a := (E (n - 1)).1) ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [hval, hm]
    fin_cases m
    · exact absurd (show cornerAngle (D.model.pts (0 + 1)) (D.model.pts 0)
        (D.model.pts (0 + 2)) = α from hα') (fun heq => hcard (heq ▸ h.1))
    · exact hβ'
    · exact absurd (show cornerAngle (D.model.pts (2 + 1)) (D.model.pts 2)
        (D.model.pts (2 + 2)) = γ from hγ') (fun heq => hcard (heq ▸ h.2.2.1))
  -- cascade: start presents α (≠ γ via hαγ), end presents β (≠ γ via hβγ)
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
      exact hαγ (hW ▸ hbα).symm  -- start presents α, not γ
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
      exact hβγ (hEn ▸ hbβ).symm  -- end presents β, not γ
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
  exact cascade n hn0 place hplace hinj hends

end Erdos634.Geometry.Dissection
