module

public import Certificates.Kernel.J4Q.IsetAll
public import Certificates.Kernel.J4Q.X0OrbOk
public import Certificates.Kernel.J4Q.MaskU
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.IS CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem nblt_false {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (lt_of_blt hb) (by omega)

theorem iAt_spec {k : Nat} (hk : k < 43264) : iAtK k = true := by
  have hc : Nat.div k 64 < 676 := by change k / 64 < 676; omega
  have h := allR_spec (ic_spec hc) (Nat.mod k 64) (by change k % 64 < 64; omega)
  have e : Nat.add (Nat.mul 64 (Nat.div k 64)) (Nat.mod k 64) = k := by
    change 64 * (k / 64) + k % 64 = k
    omega
  rw [e] at h
  exact h

theorem lpl_chk : allR 6 (fun g => andB (letterTab (letters.getD g 0) == unpackP (getN 0 LPL g))
    (letterTab (-(letters.getD g 0)) == unpackP (getN 0 LPL (Nat.mod (Nat.add g 3) 6)))) = true := by quickRfl

theorem idT_eq : idT = unpackP idP := beq_iff_eq.1 (by quickRfl)

theorem letConj_eq {g : Nat} (hg : g < 6) (p : Nat) :
    letConj (letters.getD g 0) (unpackP p) = unpackP (lcB g p) := by
  have h := allR_spec lpl_chk g hg
  beta_reduce at h
  rw [andB_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  unfold letConj lcB
  rw [h.1, h.2, compB_sound, compB_sound]

theorem iAt_dec {k : Nat} (hk : k < 43264) :
    (192 ≤ k → iPar k < k ∧ iLab k < 6 ∧ iKey k = lcB (iLab k) (iKey (iPar k))) ∧
    (192 ≤ k → k + 1 < 43264 → iPL k < iPL (k + 1)) ∧
    iKey k < 2 ^ 121 ∧ compB (iKey k) (iKey k) = idP ∧
    (∀ g < 6, iTT k g < 43264 ∧ (iTT k g < 192 ∨ iPL (iTT k g) ≤ 6 * k + g) ∧
      lcB g (iKey k) = iKey (iTT k g)) ∧
    (iSig k < 43264 ∧ iSigI k < 43264 ∧ iSig (iSigI k) = k) ∧
    (k + 1 < 43264 → iKey (iSig k) < iKey (iSig (k + 1))) := by
  have h := iAt_spec hk
  unfold iAtK at h
  beta_reduce at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, ⟨h6, h7, h8⟩, h9⟩ := h
  refine ⟨fun hk1 => ?_, fun hk1 hk2 => ?_, ?_, Nat.eq_of_beq_eq_true h4, fun g hg => ?_,
    ⟨lt_of_blt h6, lt_of_blt h7, Nat.eq_of_beq_eq_true h8⟩, fun hk2 => ?_⟩
  · rw [nblt_false hk1] at h1
    change ((iPar k).blt k && ((iLab k).blt 6 && (iKey k).beq (lcB (iLab k) (iKey (iPar k))))) = true at h1
    simp only [Bool.and_eq_true] at h1
    exact ⟨lt_of_blt h1.1, lt_of_blt h1.2.1, Nat.eq_of_beq_eq_true h1.2.2⟩
  · rw [nblt_false hk1, nbeq_false (by omega : Nat.succ k ≠ 43264)] at h2
    exact lt_of_blt h2
  · have := lt_of_blt h3
    simpa [Nat.shiftLeft_eq] using this
  · have hg' := allR_spec h5 g hg
    beta_reduce at hg'
    simp only [orB_eq'', andB_eq, Bool.and_eq_true, Bool.or_eq_true] at hg'
    obtain ⟨⟨a1, a2⟩, a3⟩ := hg'
    refine ⟨lt_of_blt a1, ?_, Nat.eq_of_beq_eq_true a3⟩
    rcases a2 with a2 | a2
    · exact Or.inl (lt_of_blt a2)
    · exact Or.inr (Nat.le_of_ble_eq_true a2)
  · rw [nbeq_false (by omega : Nat.succ k ≠ 43264)] at h9
    exact lt_of_blt h9

theorem iPL_split (k : Nat) : iPar k * 6 + iLab k = iPL k := by
  unfold iPar iLab
  change iPL k / 6 * 6 + iPL k % 6 = iPL k
  omega

theorem mono_lt {f : Nat → Nat} {n : Nat} (h : ∀ a, a + 1 < n → f a < f (a + 1)) :
    ∀ {a b : Nat}, a < b → b < n → f a < f b := by
  intro a b hab hbn
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
    · exact lt_trans (ih h' (by omega)) (h b hbn)
    · rw [h']
      exact h b hbn

theorem iKey_inj {i j : Nat} (hi : i < 43264) (hj : j < 43264) (h : iKey i = iKey j) : i = j := by
  have hs : ∀ a, a + 1 < 43264 → iKey (iSig a) < iKey (iSig (a + 1)) := fun a ha =>
    (iAt_dec (k := a) (by omega)).2.2.2.2.2.2 ha
  obtain ⟨-, hi1, hi2⟩ := (iAt_dec hi).2.2.2.2.2.1
  obtain ⟨-, hj1, hj2⟩ := (iAt_dec hj).2.2.2.2.2.1
  rw [← hi2, ← hj2] at h ⊢
  rcases Nat.lt_trichotomy (iSigI i) (iSigI j) with hl | he | hl
  · exact absurd h (Nat.ne_of_lt (mono_lt (f := fun a => iKey (iSig a)) hs hl hj1))
  · rw [he]
  · exact absurd h.symm (Nat.ne_of_lt (mono_lt (f := fun a => iKey (iSig a)) hs hl hi1))

theorem iTS_inj {i j : Nat} (hi : i < 43264) (hj : j < 43264) (h : iTS i = iTS j) : i = j :=
  iKey_inj hi hj (unpackP_inj (iAt_dec hi).2.2.1 (iAt_dec hj).2.2.1 h)

theorem seeds_chk : ((mkTL.filter fun t => compT t t == idT).eraseDups == (List.range 192).map iTS) = true := by
  quickRfl

theorem seeds_eq : invSeedsT.eraseDups = (List.range 192).map iTS := by
  unfold invSeedsT
  rw [tabL_eq]
  exact beq_iff_eq.1 seeds_chk

theorem iset_tree : ∀ k, 192 ≤ k → k < 43264 → iPar k < k ∧ iLab k < 6 ∧
    iTS k = letConj (letters.getD (iLab k) 0) (iTS (iPar k)) := fun k hk1 hk2 => by
  obtain ⟨a, b, c'⟩ := (iAt_dec hk2).1 hk1
  refine ⟨a, b, ?_⟩
  unfold iTS
  rw [letConj_eq b, c']

theorem iset_clos : ∀ k < 43264, ∀ g < 6, iTT k g < 43264 ∧
    letConj (letters.getD g 0) (iTS k) = iTS (iTT k g) := fun k hk g hg => by
  have h := (iAt_dec hk).2.2.2.2.1 g hg
  refine ⟨h.1, ?_⟩
  unfold iTS
  rw [letConj_eq hg, h.2.2]

theorem iset_ord : ∀ k, 192 ≤ k → k + 1 < 43264 →
    iPar k * 6 + iLab k < iPar (k + 1) * 6 + iLab (k + 1) := fun k hk1 hk2 => by
  rw [iPL_split, iPL_split]
  exact (iAt_dec (k := k) (by omega)).2.1 hk1 hk2

theorem iset_first : ∀ k < 43264, ∀ g < 6,
    iTT k g < 192 ∨ iPar (iTT k g) * 6 + iLab (iTT k g) ≤ k * 6 + g := fun k hk g hg => by
  have h := ((iAt_dec hk).2.2.2.2.1 g hg).2.1
  rcases h with h | h
  · exact Or.inl h
  · right
    rw [iPL_split]
    omega

theorem iset_eq : isetT = (List.range 43264).map iTS := by
  unfold isetT
  exact closure_sound (s := 192) (PAR := iPar) (LAB := iLab) (TT := iTT) seeds_eq
    (by decide) (fun i hi j hj h => iTS_inj hi hj h) iset_tree iset_clos iset_ord iset_first (by decide)

theorem mem_iset {t : List Nat} : t ∈ isetT ↔ ∃ k < 43264, iTS k = t := by
  rw [iset_eq, List.mem_map]
  simp only [List.mem_range]

theorem iset_ok : chkIset = true := by
  have hc : ∀ x, isetSet.contains x = isetT.contains x := fun x => Std.HashSet.contains_ofList
  unfold chkIset
  simp only [Bool.and_eq_true, List.all_eq_true, hc, List.contains_iff_mem, beq_iff_eq]
  refine ⟨fun s hs => ?_, fun t ht => ?_⟩
  · have h : s ∈ invSeedsT.eraseDups := List.mem_eraseDups.2 hs
    rw [seeds_eq, List.mem_map] at h
    obtain ⟨k, hk, rfl⟩ := h
    exact mem_iset.2 ⟨k, by have := List.mem_range.1 hk; omega, rfl⟩
  · obtain ⟨k, hk, rfl⟩ := mem_iset.1 ht
    refine ⟨?_, fun ℓ hℓ => ?_⟩
    · unfold iTS
      rw [← compB_sound, (iAt_dec hk).2.2.2.1, ← idT_eq]
    obtain ⟨g, hg, rfl⟩ : ∃ g < 6, letters.getD g 0 = ℓ := by
      simp only [letters, List.mem_cons, List.not_mem_nil, or_false] at hℓ
      rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨3, by decide, rfl⟩
      · exact ⟨4, by decide, rfl⟩
      · exact ⟨5, by decide, rfl⟩
    have h := iset_clos k hk g hg
    rw [h.2]
    exact mem_iset.2 ⟨_, h.1, rfl⟩

end CertificateChecks.KernelJ4Q

end
