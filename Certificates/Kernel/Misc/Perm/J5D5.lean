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

theorem pCG5 : ∀ k < 3, permB 315 9 (CGP5 k) = true := (allN_iff _ _).1 (by quickRfl)

theorem pDG5 : ∀ k < 2, permB 315 9 (DGP5 k) = true := (allN_iff _ _).1 (by quickRfl)

theorem cpart5 : j2FiveCPart 5 300 (j2FiveCCert 5) = true := by
  have hs : (j2FiveCG 5).size = 3 := by decide
  simp only [j2FiveCPart, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨enumC5, bC5.1⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hCG5 k hk, hLX 5 (by norm_num)]
    rw [hs] at hk
    interval_cases k <;> exact comm_of (by quickRfl) (pLX 5 (by norm_num)) (by quickRfl)
  · rw [allLt_iff]
    intro k hk
    rw [hCG5 k hk]
    rw [hs] at hk
    interval_cases k <;> exact inR_of (by quickRfl) (by quickRfl)

@[expose] noncomputable def qb5 (k : ℕ) : Bool :=
  !(Nat.beq (cm (C5P.F k) (QG 0)) (cm (QG 0) (C5P.F k)) &&
    Nat.beq (cm (C5P.F k) (QG 1)) (cm (QG 1) (C5P.F k))) || memK 25 QP.F (C5P.F k)

theorem qb5_0 : allR 0 60 qb5 = true := by quickRfl
theorem qb5_1 : allR 60 60 qb5 = true := by quickRfl
theorem qb5_2 : allR 120 60 qb5 = true := by quickRfl
theorem qb5_3 : allR 180 60 qb5 = true := by quickRfl
theorem qb5_4 : allR 240 60 qb5 = true := by quickRfl

theorem qb5_All : ∀ k < 300, qb5 k = true :=
  forall_of_chunks 60 5 _ fun c hc => by
    interval_cases c
    · exact qb5_0
    · exact qb5_1
    · exact qb5_2
    · exact qb5_3
    · exact qb5_4

theorem qpart5a : CFSG.KC.LQT.P.allN 2 (fun k => memK 300 C5P.F (QG k)) = true := by quickRfl

theorem qpart5 : j2FiveQPart 300 (j2FiveCCert 5) j2FiveQCert = true := by
  simp only [j2FiveQPart, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hQG k hk, any_eqA_unpack' hw bC5.1 bC5.2.1 pC5 (pQG k hk)]
    exact (allN_iff _ _).1 qpart5a k hk
  · rw [allLt_iff]
    intro k hk
    rw [bC5.2.1 k hk, hQG 0 (by norm_num), hQG 1 (by norm_num),
      comm_eq (pC5 k hk) (pQG 0 (by norm_num)), comm_eq (pC5 k hk) (pQG 1 (by norm_num)),
      any_eqA_unpack' hw bQ.1 bQ.2.1 pQ (pC5 k hk)]
    exact qb5_All k hk

theorem d5a : CFSG.KC.LQT.P.allN 2 (fun k => memK 300 C5P.F (DGP5 k)) = true := by quickRfl

theorem d5b : CFSG.KC.LQT.P.allN 2 (fun k => Nat.beq (Nat.shiftRight (DGP5 k) (315 * 9)) 0 &&
    sP (DGP5 k)) = true := by quickRfl

theorem d5c : CFSG.KC.LQT.P.allN 3 (fun k => CFSG.KC.LQT.P.allN 2 fun l =>
    memK 60 D5P.F (cj (CGP5 k) (DGP5 l))) = true := by quickRfl

theorem d5d : CFSG.KC.LQT.P.anyN 2 (fun k => CFSG.KC.LQT.P.anyN 2 fun l =>
    !(Nat.beq (cm (DGP5 k) (DGP5 l)) (cm (DGP5 l) (DGP5 k)))) = true := by quickRfl

@[expose] noncomputable def wd5 (k : ℕ) : Bool :=
  Nat.beq (D5P.F k) I || ((j2FiveSimpSel 5 k).all (fun j => decide (j < 60)) &&
    Nat.beq (j2FiveSimpW 5 k).length 2 && CFSG.KC.LQT.P.allN 2 fun l =>
      lettersOK (j2FiveSimpSel 5 k).length (j2FiveSimpW 5 k)[l]! &&
        Nat.beq (DGP5 l) (wordK 315 9 (mask 9) (pidn 315 9) (selC D5P.F k (j2FiveSimpSel 5 k))
          (selCI D5P.F k (j2FiveSimpSel 5 k)) (j2FiveSimpW 5 k)[l]!))

theorem wd5_0 : allR 0 30 wd5 = true := by quickRfl
theorem wd5_1 : allR 30 30 wd5 = true := by quickRfl

theorem words5 : conjWordsOK 315 (j2FiveDCert 5) (j2FiveDG 5) (j2FiveSimpSel 5)
    (j2FiveSimpW 5) = true := by
  have hs : (j2FiveDG 5).size = 2 := by decide
  have hall : ∀ k < 60, wd5 k = true := forall_of_chunks 30 2 _ fun c hc => by
    interval_cases c
    · exact wd5_0
    · exact wd5_1
  rw [conjWordsOK, bD5.1, allLt_iff]
  intro k hk
  have h := hall k hk
  rw [wd5, Bool.or_eq_true] at h
  rw [Bool.or_eq_true, bD5.2.1 k hk, hI, eqA_unpack' hw (pD5 k hk) pI]
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
  have hcs := conjSel_get bD5.1 bD5.2.1 pD5 hk hsel
  refine ⟨hlet, ?_⟩
  rw [hDG5 l (by rw [hs]; exact hl), wordA_unpack hw (fun h hh => (hcs h hh).1)
    (fun h hh => (hcs h hh).2.1) (fun h hh => (hcs h hh).2.2.1) (fun h hh => (hcs h hh).2.2.2)
    hlet, eqA_unpack' hw (pDG5 l hl) (permB_wordK hw (fun h hh => (hcs h hh).2.2.1)
      (fun h hh => (hcs h hh).2.2.2) hlet)]
  exact heq

@[expose] noncomputable def cd5 (k : ℕ) : Bool :=
  !(CFSG.KC.LQT.P.allN 2 fun l => Nat.beq (cm (C5P.F k) (DGP5 l)) (cm (DGP5 l) (C5P.F k))) ||
    CFSG.KC.LQT.P.anyN 5 fun e => Nat.beq (C5P.F k) (pw (LX 5) e)

theorem cd5_0 : allR 0 60 cd5 = true := by quickRfl
theorem cd5_1 : allR 60 60 cd5 = true := by quickRfl
theorem cd5_2 : allR 120 60 cd5 = true := by quickRfl
theorem cd5_3 : allR 180 60 cd5 = true := by quickRfl
theorem cd5_4 : allR 240 60 cd5 = true := by quickRfl

theorem cd5_All : ∀ k < 300, cd5 k = true :=
  forall_of_chunks 60 5 _ fun c hc => by
    interval_cases c
    · exact cd5_0
    · exact cd5_1
    · exact cd5_2
    · exact cd5_3
    · exact cd5_4

theorem bad5 : j2FiveBadCheck 5 (j2FiveCCert 5) (j2FiveDCert 5) j2FiveQCert = true := by
  have hs : (j2FiveDG 5).size = 2 := by decide
  have hcs : (j2FiveCG 5).size = 3 := by decide
  simp only [j2FiveBadCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨cpart5, qpart5⟩, enumD5⟩, bD5.1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, words5⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hDG5 k hk, any_eqA_unpack' hw bC5.1 bC5.2.1 pC5 (pDG5 k (by rw [← hs]; exact hk))]
    exact (allN_iff _ _).1 d5a k (by rw [← hs]; exact hk)
  · rw [allLt_iff]
    intro k hk
    have h := (allN_iff _ _).1 d5b k (by rw [← hs]; exact hk)
    rw [Bool.and_eq_true] at h
    rw [hDG5 k hk]
    exact inP_of h.1 (range_of_permOK (pDG5 k (by rw [← hs]; exact hk))) h.2
  · rw [allLt_iff]
    intro k hk
    rw [allLt_iff]
    intro l hl
    rw [hCG5 k hk, hDG5 l hl, conj_eq (pCG5 k (by rw [← hcs]; exact hk))
      (pDG5 l (by rw [← hs]; exact hl)), any_eqA_unpack' hw bD5.1 bD5.2.1 pD5
      (pCj (pCG5 k (by rw [← hcs]; exact hk)) (pDG5 l (by rw [← hs]; exact hl)))]
    exact (allN_iff _ _).1 ((allN_iff _ _).1 d5c k (by rw [← hcs]; exact hk)) l
      (by rw [← hs]; exact hl)
  · obtain ⟨k, hk, h⟩ := (anyN_iff _ _).1 d5d
    obtain ⟨l, hl, h⟩ := (anyN_iff _ _).1 h
    refine List.any_eq_true.2 ⟨k, List.mem_range.2 (by rw [hs]; exact hk), List.any_eq_true.2
      ⟨l, List.mem_range.2 (by rw [hs]; exact hl), ?_⟩⟩
    rw [hDG5 k (by rw [hs]; exact hk), hDG5 l (by rw [hs]; exact hl),
      comm_eq (pDG5 k hk) (pDG5 l hl)]
    exact h
  · rw [allLt_iff]
    intro k hk
    have h := cd5_All k hk
    rw [cd5, Bool.or_eq_true] at h
    rw [Bool.or_eq_true, bC5.2.1 k hk]
    rcases h with h | h
    · left
      rw [Bool.not_eq_true'] at h ⊢
      rw [Bool.eq_false_iff] at h ⊢
      intro h2
      apply h
      rw [allN_iff]
      intro l hl
      have h3 := allLt_iff.1 h2 l (by rw [hs]; exact hl)
      rw [hDG5 l (by rw [hs]; exact hl), comm_eq (pC5 k hk) (pDG5 l hl)] at h3
      exact h3
    · right
      obtain ⟨e, he, h⟩ := (anyN_iff _ _).1 h
      refine List.any_eq_true.2 ⟨e, List.mem_range.2 he, ?_⟩
      rw [hLX 5 (by norm_num), pow_eq (pLX 5 (by norm_num)),
        eqA_unpack' hw (pC5 k hk) (pPw (pLX 5 (by norm_num)) e)]
      exact h

end CertificateChecks.KernelMisc.J2F

end
