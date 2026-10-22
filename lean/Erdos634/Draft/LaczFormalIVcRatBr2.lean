-- Draft/LaczFormalIVcRatBr2.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE `VWTiling.ofPolyTiling`, stage Br2 (B-a: the cells/pieces of one c-pair).
--   Tile type (uniform for alpha = pi/2 and alpha = pi/6): labels rho (right angle, side opposite = hypotenuse = 2s), pi (30 degree vertex, opposite side = short leg s), 2 (60 degree, gamma; slen 2 ^ 2 = 3 s^2).
--   `pair_tile_shape`: a c-pair of tiles (TriStep data of `pair_shape_tiles`) is a KITE (union of the two tile carriers = `KiteData s`.set, apex V = the pi-vertex, base midpoint W = the rho-vertex)
--   or a PARALLELOGRAM (union = R1.set u R2.set, two rhombi of side s with disjoint interiors), together with the label correspondence of the corners at the two ends of the c-edge.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3, Lemma 4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatBr1
import Erdos634.Draft.LaczFormalRG12ShapeTile

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem fin3_cover : ∀ a b c d : Fin 3, a ≠ b → a ≠ c → b ≠ c → d ≠ c → d = a ∨ d = b := by decide
theorem fin3_lab : ∀ ρ π lU lV : Fin 3, ρ ≠ π → ρ ≠ 2 → π ≠ 2 → lU ≠ 2 → lV ≠ 2 → lU ≠ lV →
    (lU = ρ ∧ lV = π) ∨ (lU = π ∧ lV = ρ) := by decide
theorem fin3_third : ∀ a b : Fin 3, a ≠ b → ∃ c, c ≠ a ∧ c ≠ b := by decide
theorem fin3_two : ∀ ρ π l : Fin 3, ρ ≠ π → ρ ≠ 2 → π ≠ 2 → l ≠ 2 → l = ρ ∨ l = π := by decide

theorem tile_dsq (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (i : Fin N) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (((D.tile i).pts a) 0 - ((D.tile i).pts b) 0) ^ 2 + (((D.tile i).pts a) 1 - ((D.tile i).pts b) 1) ^ 2 = slen D (idx i c) ^ 2 := by
  rw [← dist_sq_plane, hidx, dist_model_opp D _ _ _ ((idx i).injective.ne hab) ((idx i).injective.ne hbc) ((idx i).injective.ne hac)]

theorem third_label (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (h0 : slen D 0 ≠ slen D 2) (h1 : slen D 1 ≠ slen D 2) (i : Fin N) {kk f g : Fin 3} (hkf : kk ≠ f)
    (hd : dist ((D.tile i).pts kk) ((D.tile i).pts f) = slen D 2) (hg : idx i g = 2) : g ≠ kk ∧ g ≠ f := by
  obtain ⟨c, hck, hcf⟩ := fin3_third kk f hkf
  have e : dist ((D.tile i).pts kk) ((D.tile i).pts f) = slen D (idx i c) := by
    rw [hidx]; exact dist_model_opp D _ _ _ ((idx i).injective.ne hkf) ((idx i).injective.ne hcf.symm) ((idx i).injective.ne hck.symm)
  have hc2 : idx i c = 2 := opp_eq_two D h0 h1 _ (e.symm.trans hd)
  have hgc : g = c := (idx i).injective (hg.trans hc2.symm)
  subst hgc
  exact ⟨hck, hcf⟩

/-- Foot of the perpendicular: `U` is the right-angle vertex. -/
theorem kite_foot_U {s : ℝ} (hs : 0 < s) (U V W W' : Plane) (hN : (V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2 = 3 * s ^ 2)
    (hWU : (W 0 - U 0) ^ 2 + (W 1 - U 1) ^ 2 = s ^ 2) (hWV : (W 0 - V 0) ^ 2 + (W 1 - V 1) ^ 2 = (2 * s) ^ 2)
    (h0 : ((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) * (W' 0 - U 0) = 2 * ((V 0 - U 0) * (W 0 - U 0) + (V 1 - U 1) * (W 1 - U 1)) * (V 0 - U 0) - ((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) * (W 0 - U 0))
    (h1 : ((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) * (W' 1 - U 1) = 2 * ((V 0 - U 0) * (W 0 - U 0) + (V 1 - U 1) * (W 1 - U 1)) * (V 1 - U 1) - ((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) * (W 1 - U 1)) :
    2 * U 0 = W 0 + W' 0 ∧ 2 * U 1 = W 1 + W' 1 := by
  have hd : (V 0 - U 0) * (W 0 - U 0) + (V 1 - U 1) * (W 1 - U 1) = 0 := by nlinarith
  rw [hN, hd] at h0 h1
  have h3 : (3 * s ^ 2) ≠ 0 := by positivity
  constructor
  · have : (3 * s ^ 2) * (W' 0 + W 0 - 2 * U 0) = (3 * s ^ 2) * 0 := by linear_combination h0
    have := mul_left_cancel₀ h3 this
    linarith
  · have : (3 * s ^ 2) * (W' 1 + W 1 - 2 * U 1) = (3 * s ^ 2) * 0 := by linear_combination h1
    have := mul_left_cancel₀ h3 this
    linarith

/-- Foot of the perpendicular: `V` is the right-angle vertex. -/
theorem kite_foot_V {s : ℝ} (hs : 0 < s) (U V W W' : Plane) (hN : (V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2 = 3 * s ^ 2)
    (hWV : (W 0 - V 0) ^ 2 + (W 1 - V 1) ^ 2 = s ^ 2) (hWU : (W 0 - U 0) ^ 2 + (W 1 - U 1) ^ 2 = (2 * s) ^ 2)
    (h0 : ((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) * (W' 0 - U 0) = 2 * ((V 0 - U 0) * (W 0 - U 0) + (V 1 - U 1) * (W 1 - U 1)) * (V 0 - U 0) - ((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) * (W 0 - U 0))
    (h1 : ((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) * (W' 1 - U 1) = 2 * ((V 0 - U 0) * (W 0 - U 0) + (V 1 - U 1) * (W 1 - U 1)) * (V 1 - U 1) - ((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) * (W 1 - U 1)) :
    2 * V 0 = W 0 + W' 0 ∧ 2 * V 1 = W 1 + W' 1 := by
  have hd : (V 0 - U 0) * (W 0 - U 0) + (V 1 - U 1) * (W 1 - U 1) = 3 * s ^ 2 := by nlinarith
  rw [hN, hd] at h0 h1
  have h3 : (3 * s ^ 2) ≠ 0 := by positivity
  constructor
  · have : (3 * s ^ 2) * (W' 0 + W 0 - 2 * V 0) = (3 * s ^ 2) * 0 := by linear_combination h0
    have := mul_left_cancel₀ h3 this
    linarith
  · have : (3 * s ^ 2) * (W' 1 + W 1 - 2 * V 1) = (3 * s ^ 2) * 0 := by linear_combination h1
    have := mul_left_cancel₀ h3 this
    linarith



/-- Output of a mirror (kite) pair of tiles `i, j`: the kite piece (apex V = the pi-vertex of both tiles, base midpoint W = the rho-vertex of both) and the label-preserving corner correspondence. -/
def KitePair (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (s : ℝ) (ρ π : Fin 3) (i j : Fin N) : Prop :=
  ∃ K : KiteData s, (∃ a, (D.tile i).pts a = K.V ∧ idx i a = π) ∧ (∃ a, (D.tile j).pts a = K.V ∧ idx j a = π) ∧
    (∃ a, (D.tile i).pts a = K.W ∧ idx i a = ρ) ∧ (∃ a, (D.tile j).pts a = K.W ∧ idx j a = ρ) ∧
    K.set = (D.tile i).carrier ∪ (D.tile j).carrier ∧
    (∀ a, idx i a ≠ 2 → ∃ a', (D.tile j).pts a' = (D.tile i).pts a ∧ idx j a' = idx i a)

/-- Output of a point-symmetric (parallelogram) pair: two rhombi, and the corner correspondence with the types swapped. -/
def ParPair (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (s : ℝ) (i j : Fin N) : Prop :=
  (∃ R1 R2 : RhombData s, Disjoint (interior R1.set) (interior R2.set) ∧ R1.set ∪ R2.set = (D.tile i).carrier ∪ (D.tile j).carrier) ∧
    (∀ a, idx i a ≠ 2 → ∃ a', (D.tile j).pts a' = (D.tile i).pts a ∧ idx j a' ≠ idx i a ∧ idx j a' ≠ 2)

/-- The kite of a mirror pair: tile `i` with vertices `rv` (label rho), `pv` (label pi), `g` (label 2); tile `j` with `rv', pv', g'` at the same points `R, P`; `2R = W + W'`. -/
theorem core_kite (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {s : ℝ} (hs : 0 < s) {ρ π : Fin 3} {i j : Fin N} {rv pv g rv' pv' g' : Fin 3}
    (h1 : rv ≠ pv) (h2 : rv ≠ g) (h3 : pv ≠ g) (h1' : rv' ≠ pv') (h2' : rv' ≠ g') (h3' : pv' ≠ g')
    (hrv : idx i rv = ρ) (hpv : idx i pv = π) (hg : idx i g = 2) (hrv' : idx j rv' = ρ) (hpv' : idx j pv' = π) (hg' : idx j g' = 2)
    (hlρ : slen D ρ = 2 * s) (hlπ : slen D π = s) (hl2 : slen D 2 ^ 2 = 3 * s ^ 2)
    (hR : (D.tile j).pts rv' = (D.tile i).pts rv) (hP : (D.tile j).pts pv' = (D.tile i).pts pv)
    (hmid0 : 2 * ((D.tile i).pts rv) 0 = ((D.tile i).pts g) 0 + ((D.tile j).pts g') 0)
    (hmid1 : 2 * ((D.tile i).pts rv) 1 = ((D.tile i).pts g) 1 + ((D.tile j).pts g') 1) :
    KitePair D idx s ρ π i j := by
  have dQP := tile_dsq D idx hidx i (a := g) (b := pv) (c := rv) h3.symm h2.symm h1.symm
  have dQR := tile_dsq D idx hidx i (a := g) (b := rv) (c := pv) h2.symm h3.symm h1
  have dQ'P := tile_dsq D idx hidx j (a := g') (b := pv') (c := rv') h3'.symm h2'.symm h1'.symm
  rw [hrv, hlρ] at dQP
  rw [hpv, hlπ] at dQR
  rw [hrv', hlρ, hP] at dQ'P
  have e0 : ((D.tile i).pts g) 0 - ((D.tile j).pts g') 0 = 2 * (((D.tile i).pts g) 0 - ((D.tile i).pts rv) 0) := by linarith
  have e1 : ((D.tile i).pts g) 1 - ((D.tile j).pts g') 1 = 2 * (((D.tile i).pts g) 1 - ((D.tile i).pts rv) 1) := by linarith
  have dQQ : (((D.tile i).pts g) 0 - ((D.tile j).pts g') 0) ^ 2 + (((D.tile i).pts g) 1 - ((D.tile j).pts g') 1) ^ 2 = (2 * s) ^ 2 := by
    rw [e0, e1]; linear_combination 4 * dQR
  obtain ⟨K, hKV, hKW, hK⟩ := kite_of_H3 hs ((D.tile i).pts pv) ((D.tile i).pts g) ((D.tile j).pts g') ((D.tile i).pts rv) hmid0 hmid1
    dQP dQ'P dQQ
  refine ⟨K, ⟨pv, hKV.symm, hpv⟩, ⟨pv', hP.trans hKV.symm, hpv'⟩, ⟨rv, hKW.symm, hrv⟩, ⟨rv', hR.trans hKW.symm, hrv'⟩, ?_, ?_⟩
  · ext x
    simp only [Set.mem_union]
    rw [hK x, tri_mem_abc (D.tile i) h1 h2 h3 x, tri_mem_abc (D.tile j) h1' h2' h3' x, hR, hP]
    rfl
  · intro a ha
    rcases fin3_cover rv pv g a h1 h2 h3 (by intro e; apply ha; rw [e, hg]) with rfl | rfl
    · exact ⟨rv', hR, by rw [hrv', hrv]⟩
    · exact ⟨pv', hP, by rw [hpv, hpv']⟩

/-- The two rhombi of a point-symmetric pair: tile `i` has `rv, pv, g`; tile `j` has `a1` (at the point of `rv`, label pi), `a2` (at `pv`, label rho), `g'`; `W' = R + P - W`. -/
theorem core_par (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {s : ℝ} (hs : 0 < s) {ρ π : Fin 3} {i j : Fin N} {rv pv g a1 a2 g' : Fin 3}
    (h1 : rv ≠ pv) (h2 : rv ≠ g) (h3 : pv ≠ g) (h1' : a1 ≠ a2) (h2' : a1 ≠ g') (h3' : a2 ≠ g')
    (hrv : idx i rv = ρ) (hpv : idx i pv = π) (hρπ : ρ ≠ π) (hρ : ρ ≠ 2) (hπ : π ≠ 2) (ha1 : idx j a1 = π) (ha2 : idx j a2 = ρ)
    (hlρ : slen D ρ = 2 * s) (hlπ : slen D π = s) (hl2 : slen D 2 ^ 2 = 3 * s ^ 2)
    (hR : (D.tile j).pts a1 = (D.tile i).pts rv) (hP : (D.tile j).pts a2 = (D.tile i).pts pv)
    (hg : idx i g = 2)
    (hW0 : ((D.tile j).pts g') 0 = ((D.tile i).pts rv) 0 + ((D.tile i).pts pv) 0 - ((D.tile i).pts g) 0)
    (hW1 : ((D.tile j).pts g') 1 = ((D.tile i).pts rv) 1 + ((D.tile i).pts pv) 1 - ((D.tile i).pts g) 1) :
    ParPair D idx s i j := by
  have dRQ := tile_dsq D idx hidx i (a := rv) (b := g) (c := pv) h2 h1 h3.symm
  have dPQ := tile_dsq D idx hidx i (a := pv) (b := g) (c := rv) h3 h1.symm h2.symm
  have dRP := tile_dsq D idx hidx i (a := rv) (b := pv) (c := g) h1 h2 h3
  rw [hpv, hlπ] at dRQ
  rw [hrv, hlρ] at dPQ
  rw [hg] at dRP
  have hRP : (((D.tile i).pts rv) 0 - ((D.tile i).pts pv) 0) ^ 2 + (((D.tile i).pts rv) 1 - ((D.tile i).pts pv) 1) ^ 2 = 3 * s ^ 2 := by
    rw [dRP]; exact hl2
  have hAB : (((D.tile i).pts rv) 0 - ((D.tile i).pts g) 0) * (((D.tile i).pts pv) 0 - ((D.tile i).pts g) 0) +
      (((D.tile i).pts rv) 1 - ((D.tile i).pts g) 1) * (((D.tile i).pts pv) 1 - ((D.tile i).pts g) 1) = s ^ 2 := by nlinarith
  obtain ⟨R1, R2, hd, hR12⟩ := rhombs_of_H3 hs ((D.tile i).pts g) ((D.tile i).pts rv) ((D.tile i).pts pv) ((D.tile j).pts g') hW0 hW1 dRQ dPQ hAB
  refine ⟨⟨R1, R2, hd, ?_⟩, ?_⟩
  · ext x
    simp only [Set.mem_union]
    rw [hR12 x, tri_mem_abc (D.tile i) h1 h2 h3 x, tri_mem_abc (D.tile j) h1' h2' h3' x, hR, hP]
    rfl
  · intro a ha
    rcases fin3_cover rv pv g a h1 h2 h3 (by intro e; apply ha; rw [e, hg]) with rfl | rfl
    · exact ⟨a1, hR, by rw [ha1, hrv]; exact Ne.symm hρπ, by rw [ha1]; exact hπ⟩
    · exact ⟨a2, hP, by rw [ha2, hpv]; exact hρπ, by rw [ha2]; exact hρ⟩

end Erdos634.Draft.LaczFormal.RG
