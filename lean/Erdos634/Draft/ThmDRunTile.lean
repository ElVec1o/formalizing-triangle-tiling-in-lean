import Erdos634.Draft.ThmDRunLattice

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' run port, module 3: model data of the tile and the lattice triangles as tiles  (DRAFT, NOT COMPILED, UNAUDITED)

Written 2026-10-18 while the Lean slot was busy; never run through `lake`/`lean`.  Not in `All`.

Port of `SideRunGFrame` (sections 2-3: `ModelDataG`, `angle_at_vertexG`, `HasV.anglesG`) and `SideRunGLattice` (section 3:
`UTG`, `DTG`, `U_anglesG`, `D_anglesG`, `N_anglesG`) to the tile `(u², v² − u², u v)`.

* `ModelDataT D a b c α β γ` is the TILE-GENERIC form of `ModelDataG` (`ModelDataG D e f α β γ` is
  `ModelDataT D (e f) (f² − e²) f² α β γ`).  `angle_at_vertexT` and `HasV.anglesT` are the generic proofs
  (`localAngle_of_oppSideG` is already generic in `a b c α β γ`).  This is the "abstract over the tile" generalisation;
  nothing in `SideRunG` needs to change for it.
* `tile_distinct`: the three sides `u², v² − u², uv` of a coprime pair `u < v` are pairwise distinct.
* `UTT, DTT`: `U(ξ,η)` and `D(ξ,η)` are tiles; `U_anglesT, D_anglesT, N_anglesT`: their angles
  `(α,β,γ)`, `(γ,β,α)`, and `(β,γ)` at the `a`-edge of `N` (the mirror tile; third vertex `lp (ξ+2−μ) (η+μ)`).
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.TilePlacement Erdos634.Draft.SideRun Set

/-! ## 1. The tile is a tile: distinct sides -/

theorem tile_distinct {u v : ℕ} (hcop : Nat.Coprime u v) (hu : 0 < u) (huv : u < v) :
    (u : ℝ) ^ 2 ≠ (v : ℝ) ^ 2 - (u : ℝ) ^ 2 ∧ (u : ℝ) ^ 2 ≠ (u : ℝ) * v ∧
      (v : ℝ) ^ 2 - (u : ℝ) ^ 2 ≠ (u : ℝ) * v := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 : v ^ 2 = 2 * u ^ 2 := by
      have : (v : ℝ) ^ 2 = 2 * (u : ℝ) ^ 2 := by linarith
      exact_mod_cast this
    have hd : u ^ 2 ∣ v ^ 2 := ⟨2, by rw [h1]; ring⟩
    have hc : Nat.Coprime (u ^ 2) (v ^ 2) := Nat.Coprime.pow 2 2 hcop
    have h2 : u ^ 2 = 1 := hc.eq_one_of_dvd hd
    have h3 : u = 1 := by
      by_contra hne
      have h2u : 2 ≤ u := by omega
      nlinarith
    subst h3
    nlinarith
  · intro h
    have : (u : ℝ) * (u - v) = 0 := by linarith
    have hne : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
    have : (u : ℝ) - v = 0 := (mul_eq_zero.mp this).resolve_left hne
    have : (u : ℝ) = v := by linarith
    have : u = v := by exact_mod_cast this
    omega
  · intro h
    have h1 : v ^ 2 = u * (u + v) := by
      have : (v : ℝ) ^ 2 = (u : ℝ) * ((u : ℝ) + v) := by linarith
      exact_mod_cast this
    have hd : u ∣ v ^ 2 := ⟨u + v, h1⟩
    have hc : Nat.Coprime u (v ^ 2) := Nat.Coprime.pow_right 2 hcop
    have h2 : u = 1 := hc.eq_one_of_dvd hd
    subst h2
    nlinarith

/-! ## 2. Generic model data -/

/-- the model of the dissection `D` is the tile with opposite sides `(a, b, c)` and corner angles `α, β, γ` -/
structure ModelDataT {N : ℕ} (D : CongruentDissection N) (a b c α β γ : ℝ) : Prop where
  hs0 : sideOpp D.model 0 = a
  hs1 : sideOpp D.model 1 = b
  hs2 : sideOpp D.model 2 = c
  hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α
  hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β
  hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ

/-- **The local angle at a vertex, read off the opposite side** (generic form of `angle_at_vertexG`). -/
theorem angle_at_vertexT {N : ℕ} (D : CongruentDissection N) {a b c α β γ : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hM : ModelDataT D a b c α β γ) (i : Fin N)
    {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j) :
    (dist ((D.tile i).pts m) ((D.tile i).pts j) = a → (D.tile i).localAngle ((D.tile i).pts k) = α) ∧
    (dist ((D.tile i).pts m) ((D.tile i).pts j) = b → (D.tile i).localAngle ((D.tile i).pts k) = β) ∧
    (dist ((D.tile i).pts m) ((D.tile i).pts j) = c → (D.tile i).localAngle ((D.tile i).pts k) = γ) := by
  have h := Erdos634.Draft.SideRunG.localAngle_of_oppSideG D hab hac hbc hM.hs0 hM.hs1 hM.hs2
    hM.hα' hM.hβ' hM.hγ' i k
  rcases Erdos634.MarchInduction.fin3_succ k m j hkm hkj hmj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at h; exact h
  · rw [h1, h2, dist_comm ((D.tile i).pts j) ((D.tile i).pts m)] at h; exact h

/-- the angles of a tile with three named vertices, read off the opposite sides -/
theorem _root_.Erdos634.Draft.SideRun.HasV.anglesT {N : ℕ} {D : CongruentDissection N} {t : Fin N}
    {A B C : Plane} {a b c α β γ : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hM : ModelDataT D a b c α β γ) (h : HasV D t A B C) :
    (dist B C = a → (D.tile t).localAngle A = α) ∧
    (dist B C = b → (D.tile t).localAngle A = β) ∧
    (dist B C = c → (D.tile t).localAngle A = γ) := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  have hA := angle_at_vertexT D hab hac hbc hM t hkm hkj hmj
  rw [hk, hm, hj] at hA
  exact hA

/-! ## 3. The lattice triangles as tiles, and their angles -/

variable {N : ℕ} {D : CongruentDissection N}

/-- `U(ξ,η)` is a tile -/
def UTT (D : CongruentDissection N) (u v ε x ξ η : ℝ) : Prop :=
  ∃ t, HasV D t (lpT u v ε x ξ η) (lpT u v ε x (ξ + 1) η) (lpT u v ε x ξ (η + 1))

/-- `D(ξ,η)` is a tile -/
def DTT (D : CongruentDissection N) (u v ε x ξ η : ℝ) : Prop :=
  ∃ t, HasV D t (lpT u v ε x (ξ + 1) η) (lpT u v ε x ξ (η + 1)) (lpT u v ε x (ξ + 1) (η + 1))

section angles

variable {u v ε x : ℝ} {α β γ : ℝ}

/-- the angles of `U(ξ,η)`: `α` at `lp ξ η`, `β` at `lp (ξ+1) η`, `γ` at `lp ξ (η+1)` -/
theorem U_anglesT (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1)
    (hab : u ^ 2 ≠ v ^ 2 - u ^ 2) (hac : u ^ 2 ≠ u * v) (hbc : v ^ 2 - u ^ 2 ≠ u * v)
    (hM : ModelDataT D (u ^ 2) (v ^ 2 - u ^ 2) (u * v) α β γ) {t : Fin N} {ξ η : ℝ}
    (h : HasV D t (lpT u v ε x ξ η) (lpT u v ε x (ξ + 1) η) (lpT u v ε x ξ (η + 1))) :
    (D.tile t).localAngle (lpT u v ε x ξ η) = α ∧
    (D.tile t).localAngle (lpT u v ε x (ξ + 1) η) = β ∧
    (D.tile t).localAngle (lpT u v ε x ξ (η + 1)) = γ := by
  refine ⟨(h.anglesT hab hac hbc hM).1 (dist_step_aT hu huv hv hε ξ η),
    (h.rot.anglesT hab hac hbc hM).2.1 ?_,
    (h.rot.rot.anglesT hab hac hbc hM).2.2 (dist_step_uT hu huv hv hε ξ η)⟩
  rw [dist_comm]; exact dist_step_vT hu huv hv hε ξ η

/-- the angles of `D(ξ,η)`: `γ` at `lp (ξ+1) η`, `β` at `lp ξ (η+1)`, `α` at `lp (ξ+1) (η+1)` -/
theorem D_anglesT (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1)
    (hab : u ^ 2 ≠ v ^ 2 - u ^ 2) (hac : u ^ 2 ≠ u * v) (hbc : v ^ 2 - u ^ 2 ≠ u * v)
    (hM : ModelDataT D (u ^ 2) (v ^ 2 - u ^ 2) (u * v) α β γ) {t : Fin N} {ξ η : ℝ}
    (h : HasV D t (lpT u v ε x (ξ + 1) η) (lpT u v ε x ξ (η + 1)) (lpT u v ε x (ξ + 1) (η + 1))) :
    (D.tile t).localAngle (lpT u v ε x (ξ + 1) η) = γ ∧
    (D.tile t).localAngle (lpT u v ε x ξ (η + 1)) = β ∧
    (D.tile t).localAngle (lpT u v ε x (ξ + 1) (η + 1)) = α := by
  refine ⟨(h.anglesT hab hac hbc hM).2.2 (dist_step_uT hu huv hv hε ξ (η + 1)),
    (h.rot.anglesT hab hac hbc hM).2.1 ?_,
    (h.rot.rot.anglesT hab hac hbc hM).1 (dist_step_aT hu huv hv hε ξ η)⟩
  rw [dist_comm]; exact dist_step_vT hu huv hv hε (ξ + 1) η

/-- the angles of the mirror tile `N(ξ,η)` at the ends of its `a`-edge: `β` at `lp (ξ+1) η`, `γ` at `lp ξ (η+1)` -/
theorem N_anglesT (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1)
    (hab : u ^ 2 ≠ v ^ 2 - u ^ 2) (hac : u ^ 2 ≠ u * v) (hbc : v ^ 2 - u ^ 2 ≠ u * v)
    (hM : ModelDataT D (u ^ 2) (v ^ 2 - u ^ 2) (u * v) α β γ) {t : Fin N} {ξ η : ℝ}
    (h : HasV D t (lpT u v ε x (ξ + 1) η) (lpT u v ε x ξ (η + 1))
      (lpT u v ε x (ξ + 2 - muT u v) (η + muT u v))) :
    (D.tile t).localAngle (lpT u v ε x (ξ + 1) η) = β ∧
    (D.tile t).localAngle (lpT u v ε x ξ (η + 1)) = γ := by
  refine ⟨(h.anglesT hab hac hbc hM).2.1 ?_,
    (h.rot.anglesT hab hac hbc hM).2.2 (dist_N_VT hu huv hv hε ξ η)⟩
  rw [dist_comm]; exact dist_N_GT hu huv hv hε ξ η

end angles

end Erdos634.Draft.ThmDRun

#print axioms Erdos634.Draft.ThmDRun.tile_distinct
#print axioms Erdos634.Draft.ThmDRun.angle_at_vertexT
#print axioms Erdos634.Draft.ThmDRun.U_anglesT
#print axioms Erdos634.Draft.ThmDRun.D_anglesT
#print axioms Erdos634.Draft.ThmDRun.N_anglesT
