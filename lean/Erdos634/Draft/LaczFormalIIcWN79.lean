-- Draft/LaczFormalIIcWN79.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: `KiteLayer3`, the supply with the PURE-GEOMETRY ring fields removed.
-- Compared with `KiteLayer2` (WN74) the polygon A, its strict convexity (`SC A 1`, WN78), its injectivity, the strict interiority of the cycle vertices (`inside`), the strict convexity of the corner polygon
-- (`equiangular_SC`, WN77), `hN`, the signs `tauA = 1`, `tauC = sigma` are no longer supply: `A`, `hAinj`, `hAsc`, `hinside` are DATA derived at tile level (ConvPoly, `c_pos_of_interior`) and the rest is proved here.
-- Named residue of the corner supply: `fam` (chord family of the concave corners), `chords` (the Gamma_except chords from the vertices of A: exterior to the corner polygon, pairwise disjoint) and `fig8` (shapes of the ring quadrilaterals).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, proof of Lemma 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN78

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

/-- The chords `A i -- c (w i)` leave the polygon `c` (exterior) and are pairwise disjoint (printed: "since an intersection of two of them would be an exceptional point"). -/
structure ChordsExt {M : ℕ} [NeZero M] (A c : Fin M → ℂ) (w : Fin M → Fin M) (τC : ℝ) : Prop where
  out : ∀ (i : Fin M) (s : ℝ), 0 ≤ s → s < 1 → ∃ j, τC * sideFn (c j) (c (j + 1) - c j) (A i + (s : ℂ) * (c (w i) - A i)) < 0
  disj : ∀ i j : Fin M, i ≠ j → Disjoint (segment ℝ (A i) (c (w i))) (segment ℝ (A j) (c (w j)))

/-- The residue of the corner supply for the corner polygon `q` with orientation sign `sigma`. -/
structure CornerRing3 (M : ℕ) [NeZero M] (α β γ : ℝ) (A : Fin M → ℂ) {m : ℕ} [NeZero m] (q : Fin m → ℂ) (σ : ℝ) : Prop where
  fam : ∃ J : Fin m → Fin m, ChordFam q σ J
  chords : (∀ k, σ * extAng q k = γ) → ∀ h : m = M, ∃ w : Fin M → Fin M, ChordsExt A (fun j : Fin M => q (Fin.cast h.symm j)) w σ ∧
    (((∀ i, w (i + 1) = w i + 1) ∨ (∀ i, w (i + 1) = w i - 1)) →
      ∃ d L mm : ZMod M → ℝ, ∀ i, RG.RingQuadA α β γ (L i) (d i) (mm i) (d (i - 1)) ∨ RG.RingQuadB α β γ (L i) (d i) (mm i) (d (i - 1)))

structure KiteLayer3 (M : ℕ) [NeZero M] where
  α : ℝ
  β : ℝ
  γ : ℝ
  hsum : α + β + γ = Real.pi
  hα : 0 < α
  hβ : 0 < β
  hγ : 0 < γ
  hγM : γ = 2 * Real.pi / M
  hne : α ≠ β
  hM : 3 ≤ M
  m : ℕ
  [hmne : NeZero m]
  C : Fin m → ℂ
  hm : 3 ≤ m
  hCs : SimplePoly C
  hCi : Function.Injective C
  turn : ∀ k : Fin m, extAng C k = γ ∨ extAng C k = 0 ∨ extAng C k = -γ
  A : Fin M → ℂ
  hAinj : Function.Injective A
  hAsc : SC A 1
  hinside : ∀ (j : Fin M) (k : Fin m), 0 < 1 * sideFn (A j) (A (j + 1) - A j) (C k)
  corner : ∀ (m' : ℕ) [NeZero m'] (q : Fin m' → ℂ), IsCornerOf C q → ∀ σ, OrientOK q σ → CornerRing3 M α β γ A q σ

theorem kiteLayer3_false {M : ℕ} [NeZero M] (K : KiteLayer3 M) : False := by
  haveI := K.hmne
  obtain ⟨m', hm', q, hq⟩ := exists_corner K.C K.hCs K.hCi K.hm
  obtain ⟨h3, hqs, hqi, hqne, hqe, hqv⟩ := hq
  obtain ⟨σ, hO⟩ := orient_exists hqs hqi h3
  have hCR := K.corner m' q ⟨h3, hqs, hqi, hqne, hqe, hqv⟩ σ hO
  obtain ⟨J, hJ⟩ := hCR.fam
  have hnc := no_concave hqs hqi h3 hO hJ
  have hγ := K.hγ
  have hσ := hO.1.1
  have hturn : ∀ k : Fin m', σ * extAng q k = K.γ := by
    intro k
    obtain ⟨k', -, hk'⟩ := hqv k
    have hne := hqne k
    have hnck := hnc k
    rcases K.turn k' with h | h | h
    · rcases hσ with rfl | rfl
      · rw [hk', h]; ring
      · exfalso; apply hnck; rw [hk', h]; linarith
    · exact absurd (hk'.trans h) hne
    · rcases hσ with rfl | rfl
      · exfalso; apply hnck; rw [hk', h]; linarith
      · rw [hk', h]; ring
  have hsum : ∑ k : Fin m', (Real.pi - σ * extAng q k) = ((m' : ℝ) - 2) * Real.pi := hO.2.2.1
  have hmM : m' = M := by
    have h1 : ∑ k : Fin m', (Real.pi - σ * extAng q k) = m' * (Real.pi - K.γ) := by
      rw [Finset.sum_congr rfl (fun k _ => by rw [hturn k])]
      simp
      ring
    rw [h1] at hsum
    have h2 : (m' : ℝ) * K.γ = 2 * Real.pi := by linarith
    have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    have h3' : (m' : ℝ) * (2 * Real.pi / M) = 2 * Real.pi := by rw [← K.hγM]; exact h2
    have h4 : (m' : ℝ) = M := by
      field_simp at h3'
      have hpi := Real.pi_pos
      nlinarith
    exact_mod_cast h4
  obtain ⟨w, hCE, hf8⟩ := hCR.chords hturn hmM
  subst hmM
  have hSC : SC q σ := equiangular_SC hqi h3 hσ K.hγM hturn
  have R : RingSetup K.A q w 1 σ :=
    { hN := K.hM
      τA1 := Or.inl rfl
      τC1 := hσ
      Ainj := K.hAinj
      cinj := hqi
      SA := K.hAsc
      SCc := hSC
      inside := fun j m'' => by
        obtain ⟨k, hk, -⟩ := hqv m''
        rw [hk]; exact K.hinside j k
      out := hCE.out
      disj := hCE.disj }
  have hord := R.ring_order
  obtain ⟨d, L, mm, hRq⟩ := hf8 hord
  exact RG.ring_monotone K.hsum K.hα K.hβ K.hγ K.hne d L mm hRq

#print axioms kiteLayer3_false

end Erdos634.Draft.LaczFormal.WN
