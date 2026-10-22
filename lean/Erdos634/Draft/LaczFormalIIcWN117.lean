-- Draft/LaczFormalIIcWN117.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: `KiteLayer6`, the abstract layer with the corner polygon `IsCornerOfD` (non-straight vertices and edge directions kept) and the conclusion of R4 in the disjunctive form (alpha, beta) or (beta, alpha).
-- Compared with `KiteLayer3` (WN79) the chord family of the concave corners is now a hypothesis about the CYCLE `C` itself (`fam`, proved at tile level in WN98 `r2_chordfam`), so `no_concave` is applied to `C`
-- (straight vertices are harmless there) and the corner polygon `q` only enters through the ring (R3, R4).  The sign of `q` is that of `C`: all non-zero turns of `C` are `sigma_C * gamma`, and the angle sum of `q` forces `sigma_q = sigma_C`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, proof of Lemma 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN79
import Erdos634.Draft.LaczFormalIIcWN55
import Erdos634.Draft.LaczFormalIIcWN109

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

structure KiteLayer6 (M : ℕ) [NeZero M] where
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
  fam : ∀ σ, OrientOK C σ → ∃ J : Fin m → Fin m, ChordFam C σ J
  ring : ∀ (m' : ℕ) [NeZero m'] (q : Fin m' → ℂ), IsCornerOfD C q → ∀ σ, OrientOK q σ → (∀ k, σ * extAng q k = γ) → ∀ h : m' = M,
    ∃ w : Fin M → Fin M, ChordsExt A (fun j : Fin M => q (Fin.cast h.symm j)) w σ ∧
    (((∀ i, w (i + 1) = w i + 1) ∨ (∀ i, w (i + 1) = w i - 1)) →
      (∃ d L mm : ZMod M → ℝ, ∀ i, RG.RingQuadA α β γ (L i) (d i) (mm i) (d (i - 1)) ∨ RG.RingQuadB α β γ (L i) (d i) (mm i) (d (i - 1))) ∨
      (∃ d L mm : ZMod M → ℝ, ∀ i, RG.RingQuadA β α γ (L i) (d i) (mm i) (d (i - 1)) ∨ RG.RingQuadB β α γ (L i) (d i) (mm i) (d (i - 1))))

theorem kiteLayer6_false {M : ℕ} [NeZero M] (K : KiteLayer6 M) : False := by
  haveI := K.hmne
  obtain ⟨σC, hOC⟩ := orient_exists K.hCs K.hCi K.hm
  obtain ⟨J, hJ⟩ := K.fam σC hOC
  have hnc := no_concave K.hCs K.hCi K.hm hOC hJ
  obtain ⟨m', hm', q, hqS⟩ := exists_corner_dir K.C K.hCs K.hCi K.hm
  obtain ⟨h3, hqs, hqi, hqne, hqe, hqv⟩ := hqS.1.1
  obtain ⟨σ, hO⟩ := orient_exists hqs hqi h3
  have hγ := K.hγ
  have hσ := hO.1.1
  have hσC := hOC.1.1
  have hext : ∀ j : Fin m', extAng q j = σC * K.γ := by
    intro j
    obtain ⟨k', -, hk'⟩ := hqv j
    have hne := hqne j
    have hnck := hnc k'
    rw [hk'] at hne ⊢
    rcases K.turn k' with h | h | h
    · rcases hσC with rfl | rfl
      · rw [h]; ring
      · exfalso; apply hnck; rw [h]; linarith
    · exact absurd h hne
    · rcases hσC with rfl | rfl
      · exfalso; apply hnck; rw [h]; linarith
      · rw [h]; ring
  have hsum : ∑ k : Fin m', (Real.pi - σ * extAng q k) = ((m' : ℝ) - 2) * Real.pi := hO.2.2.1
  have h1 : ∑ k : Fin m', (Real.pi - σ * extAng q k) = m' * (Real.pi - σ * (σC * K.γ)) := by
    rw [Finset.sum_congr rfl (fun k _ => by rw [hext k]), Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h1] at hsum
  have h2 : (m' : ℝ) * (σ * σC) * K.γ = 2 * Real.pi := by linarith
  have hσσ : σ * σC = 1 := by
    rcases hσ with rfl | rfl <;> rcases hσC with rfl | rfl
    · norm_num
    · exfalso
      have : (0 : ℝ) < (m' : ℝ) := by exact_mod_cast (by omega : 0 < m')
      nlinarith [Real.pi_pos]
    · exfalso
      have : (0 : ℝ) < (m' : ℝ) := by exact_mod_cast (by omega : 0 < m')
      nlinarith [Real.pi_pos]
    · norm_num
  have hturn : ∀ k : Fin m', σ * extAng q k = K.γ := by
    intro k
    rw [hext k]
    calc σ * (σC * K.γ) = (σ * σC) * K.γ := by ring
      _ = K.γ := by rw [hσσ]; ring
  have hmM : m' = M := by
    rw [hσσ] at h2
    have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    have h3' : (m' : ℝ) * (2 * Real.pi / M) = 2 * Real.pi := by rw [← K.hγM]; linarith
    have h4 : (m' : ℝ) = M := by
      field_simp at h3'
      have hpi := Real.pi_pos
      nlinarith
    exact_mod_cast h4
  obtain ⟨w, hCE, hf8⟩ := K.ring m' q hqS σ hO hturn hmM
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
  rcases hf8 hord with ⟨d, L, mm, hRq⟩ | ⟨d, L, mm, hRq⟩
  · exact RG.ring_monotone K.hsum K.hα K.hβ K.hγ K.hne d L mm hRq
  · exact RG.ring_monotone (by linarith [K.hsum]) K.hβ K.hα K.hγ K.hne.symm d L mm hRq

#print axioms kiteLayer6_false

end Erdos634.Draft.LaczFormal.WN
