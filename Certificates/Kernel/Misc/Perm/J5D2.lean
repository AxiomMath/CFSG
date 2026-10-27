module

public import Certificates.Kernel.Misc.Perm.J5H2
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.KC.Misc.Clos (allN_iff anyN_iff allR forall_of_chunks)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem pCG2 : ∀ k < 3, permB 315 9 (CGP2 k) = true := (allN_iff _ _).1 (by quickRfl)

theorem pDG2 : ∀ k < 3, permB 315 9 (DGP2 k) = true := (allN_iff _ _).1 (by quickRfl)

theorem cpart2 : j2FiveCPart 2 300 (j2FiveCCert 2) = true := by
  have hs : (j2FiveCG 2).size = 3 := by decide
  simp only [j2FiveCPart, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨enumC2, bC2.1⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hCG2 k hk, hLX 2 (by norm_num)]
    rw [hs] at hk
    interval_cases k <;> exact comm_of (by quickRfl) (pLX 2 (by norm_num)) (by quickRfl)
  · rw [allLt_iff]
    intro k hk
    rw [hCG2 k hk]
    rw [hs] at hk
    interval_cases k <;> exact inR_of (by quickRfl) (by quickRfl)

@[expose] noncomputable def qb2 (k : ℕ) : Bool :=
  !(Nat.beq (cm (C2P.F k) (QG 0)) (cm (QG 0) (C2P.F k)) &&
    Nat.beq (cm (C2P.F k) (QG 1)) (cm (QG 1) (C2P.F k))) || memK 25 QP.F (C2P.F k)

theorem qb2_0 : allR 0 60 qb2 = true := by quickRfl
theorem qb2_1 : allR 60 60 qb2 = true := by quickRfl
theorem qb2_2 : allR 120 60 qb2 = true := by quickRfl
theorem qb2_3 : allR 180 60 qb2 = true := by quickRfl
theorem qb2_4 : allR 240 60 qb2 = true := by quickRfl

theorem qb2_All : ∀ k < 300, qb2 k = true :=
  forall_of_chunks 60 5 _ fun c hc => by
    interval_cases c
    · exact qb2_0
    · exact qb2_1
    · exact qb2_2
    · exact qb2_3
    · exact qb2_4

theorem qpart2a : CFSG.KC.LQT.P.allN 2 (fun k => memK 300 C2P.F (QG k)) = true := by quickRfl

theorem qpart2 : j2FiveQPart 300 (j2FiveCCert 2) j2FiveQCert = true := by
  simp only [j2FiveQPart, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hQG k hk, any_eqA_unpack' hw bC2.1 bC2.2.1 pC2 (pQG k hk)]
    exact (allN_iff _ _).1 qpart2a k hk
  · rw [allLt_iff]
    intro k hk
    rw [bC2.2.1 k hk, hQG 0 (by norm_num), hQG 1 (by norm_num),
      comm_eq (pC2 k hk) (pQG 0 (by norm_num)), comm_eq (pC2 k hk) (pQG 1 (by norm_num)),
      any_eqA_unpack' hw bQ.1 bQ.2.1 pQ (pC2 k hk)]
    exact qb2_All k hk

theorem d2a : CFSG.KC.LQT.P.allN 3 (fun k => memK 300 C2P.F (DGP2 k)) = true := by quickRfl

theorem d2b : CFSG.KC.LQT.P.allN 3 (fun k => Nat.beq (Nat.shiftRight (DGP2 k) (315 * 9)) 0 &&
    sP (DGP2 k)) = true := by quickRfl

theorem d2c : CFSG.KC.LQT.P.allN 3 (fun k => CFSG.KC.LQT.P.allN 3 fun l =>
    memK 60 D2P.F (cj (CGP2 k) (DGP2 l))) = true := by quickRfl

theorem d2d : CFSG.KC.LQT.P.anyN 3 (fun k => CFSG.KC.LQT.P.anyN 3 fun l =>
    !(Nat.beq (cm (DGP2 k) (DGP2 l)) (cm (DGP2 l) (DGP2 k)))) = true := by quickRfl

@[expose] noncomputable def wd2 (k : ℕ) : Bool :=
  Nat.beq (D2P.F k) I || ((j2FiveSimpSel 2 k).all (fun j => decide (j < 60)) &&
    Nat.beq (j2FiveSimpW 2 k).length 3 && CFSG.KC.LQT.P.allN 3 fun l =>
      lettersOK (j2FiveSimpSel 2 k).length (j2FiveSimpW 2 k)[l]! &&
        Nat.beq (DGP2 l) (wordK 315 9 (mask 9) (pidn 315 9) (selC D2P.F k (j2FiveSimpSel 2 k))
          (selCI D2P.F k (j2FiveSimpSel 2 k)) (j2FiveSimpW 2 k)[l]!))

theorem wd2_0 : allR 0 30 wd2 = true := by quickRfl
theorem wd2_1 : allR 30 30 wd2 = true := by quickRfl

theorem words2 : conjWordsOK 315 (j2FiveDCert 2) (j2FiveDG 2) (j2FiveSimpSel 2)
    (j2FiveSimpW 2) = true := by
  have hs : (j2FiveDG 2).size = 3 := by decide
  have hall : ∀ k < 60, wd2 k = true := forall_of_chunks 30 2 _ fun c hc => by
    interval_cases c
    · exact wd2_0
    · exact wd2_1
  rw [conjWordsOK, bD2.1, allLt_iff]
  intro k hk
  have h := hall k hk
  rw [wd2, Bool.or_eq_true] at h
  rw [Bool.or_eq_true, bD2.2.1 k hk, hI, eqA_unpack' hw (pD2 k hk) pI]
  rcases h with h | h
  · exact Or.inl h
  right
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢
  obtain ⟨⟨hsel, hlen⟩, hw3⟩ := h
  refine ⟨⟨hsel, by rw [hs]; exact Nat.eq_of_beq_eq_true hlen⟩, ?_⟩
  rw [hs, allLt_iff]
  intro l hl
  have hl' := (allN_iff _ _).1 hw3 l hl
  rw [Bool.and_eq_true] at hl' ⊢
  obtain ⟨hlet, heq⟩ := hl'
  have hcs := conjSel_get bD2.1 bD2.2.1 pD2 hk hsel
  refine ⟨hlet, ?_⟩
  rw [hDG2 l (by rw [hs]; exact hl), wordA_unpack hw (fun h hh => (hcs h hh).1)
    (fun h hh => (hcs h hh).2.1) (fun h hh => (hcs h hh).2.2.1) (fun h hh => (hcs h hh).2.2.2)
    hlet, eqA_unpack' hw (pDG2 l hl) (permB_wordK hw (fun h hh => (hcs h hh).2.2.1)
      (fun h hh => (hcs h hh).2.2.2) hlet)]
  exact heq

@[expose] noncomputable def cd2 (k : ℕ) : Bool :=
  !(CFSG.KC.LQT.P.allN 3 fun l => Nat.beq (cm (C2P.F k) (DGP2 l)) (cm (DGP2 l) (C2P.F k))) ||
    CFSG.KC.LQT.P.anyN 5 fun e => Nat.beq (C2P.F k) (pw (LX 2) e)

theorem cd2_0 : allR 0 60 cd2 = true := by quickRfl
theorem cd2_1 : allR 60 60 cd2 = true := by quickRfl
theorem cd2_2 : allR 120 60 cd2 = true := by quickRfl
theorem cd2_3 : allR 180 60 cd2 = true := by quickRfl
theorem cd2_4 : allR 240 60 cd2 = true := by quickRfl

theorem cd2_All : ∀ k < 300, cd2 k = true :=
  forall_of_chunks 60 5 _ fun c hc => by
    interval_cases c
    · exact cd2_0
    · exact cd2_1
    · exact cd2_2
    · exact cd2_3
    · exact cd2_4

theorem bad2 : j2FiveBadCheck 2 (j2FiveCCert 2) (j2FiveDCert 2) j2FiveQCert = true := by
  have hs : (j2FiveDG 2).size = 3 := by decide
  have hcs : (j2FiveCG 2).size = 3 := by decide
  simp only [j2FiveBadCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨cpart2, qpart2⟩, enumD2⟩, bD2.1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, words2⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hDG2 k hk, any_eqA_unpack' hw bC2.1 bC2.2.1 pC2 (pDG2 k (by rw [← hs]; exact hk))]
    exact (allN_iff _ _).1 d2a k (by rw [← hs]; exact hk)
  · rw [allLt_iff]
    intro k hk
    have h := (allN_iff _ _).1 d2b k (by rw [← hs]; exact hk)
    rw [Bool.and_eq_true] at h
    rw [hDG2 k hk]
    exact inP_of h.1 (range_of_permOK (pDG2 k (by rw [← hs]; exact hk))) h.2
  · rw [allLt_iff]
    intro k hk
    rw [allLt_iff]
    intro l hl
    rw [hCG2 k hk, hDG2 l hl, conj_eq (pCG2 k (by rw [← hcs]; exact hk))
      (pDG2 l (by rw [← hs]; exact hl)), any_eqA_unpack' hw bD2.1 bD2.2.1 pD2
      (pCj (pCG2 k (by rw [← hcs]; exact hk)) (pDG2 l (by rw [← hs]; exact hl)))]
    exact (allN_iff _ _).1 ((allN_iff _ _).1 d2c k (by rw [← hcs]; exact hk)) l
      (by rw [← hs]; exact hl)
  · obtain ⟨k, hk, h⟩ := (anyN_iff _ _).1 d2d
    obtain ⟨l, hl, h⟩ := (anyN_iff _ _).1 h
    refine List.any_eq_true.2 ⟨k, List.mem_range.2 (by rw [hs]; exact hk), List.any_eq_true.2
      ⟨l, List.mem_range.2 (by rw [hs]; exact hl), ?_⟩⟩
    rw [hDG2 k (by rw [hs]; exact hk), hDG2 l (by rw [hs]; exact hl),
      comm_eq (pDG2 k hk) (pDG2 l hl)]
    exact h
  · rw [allLt_iff]
    intro k hk
    have h := cd2_All k hk
    rw [cd2, Bool.or_eq_true] at h
    rw [Bool.or_eq_true, bC2.2.1 k hk]
    rcases h with h | h
    · left
      rw [Bool.not_eq_true'] at h ⊢
      rw [Bool.eq_false_iff] at h ⊢
      intro h2
      apply h
      rw [allN_iff]
      intro l hl
      have h3 := allLt_iff.1 h2 l (by rw [hs]; exact hl)
      rw [hDG2 l (by rw [hs]; exact hl), comm_eq (pC2 k hk) (pDG2 l hl)] at h3
      exact h3
    · right
      obtain ⟨e, he, h⟩ := (anyN_iff _ _).1 h
      refine List.any_eq_true.2 ⟨e, List.mem_range.2 he, ?_⟩
      rw [hLX 2 (by norm_num), pow_eq (pLX 2 (by norm_num)),
        eqA_unpack' hw (pC2 k hk) (pPw (pLX 2 (by norm_num)) e)]
      exact h

end CertificateChecks.KernelMisc.J2F

end
