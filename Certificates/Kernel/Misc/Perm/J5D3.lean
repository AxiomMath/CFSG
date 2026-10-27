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

theorem pCG3 : ∀ k < 2, permB 315 9 (CGP3 k) = true := (allN_iff _ _).1 (by quickRfl)

theorem pDG3 : ∀ k < 2, permB 315 9 (DGP3 k) = true := (allN_iff _ _).1 (by quickRfl)

theorem cpart3 : j2FiveCPart 3 300 (j2FiveCCert 3) = true := by
  have hs : (j2FiveCG 3).size = 2 := by decide
  simp only [j2FiveCPart, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨enumC3, bC3.1⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hCG3 k hk, hLX 3 (by norm_num)]
    rw [hs] at hk
    interval_cases k <;> exact comm_of (by quickRfl) (pLX 3 (by norm_num)) (by quickRfl)
  · rw [allLt_iff]
    intro k hk
    rw [hCG3 k hk]
    rw [hs] at hk
    interval_cases k <;> exact inR_of (by quickRfl) (by quickRfl)

@[expose] noncomputable def qb3 (k : ℕ) : Bool :=
  !(Nat.beq (cm (C3P.F k) (QG 0)) (cm (QG 0) (C3P.F k)) &&
    Nat.beq (cm (C3P.F k) (QG 1)) (cm (QG 1) (C3P.F k))) || memK 25 QP.F (C3P.F k)

theorem qb3_0 : allR 0 60 qb3 = true := by quickRfl
theorem qb3_1 : allR 60 60 qb3 = true := by quickRfl
theorem qb3_2 : allR 120 60 qb3 = true := by quickRfl
theorem qb3_3 : allR 180 60 qb3 = true := by quickRfl
theorem qb3_4 : allR 240 60 qb3 = true := by quickRfl

theorem qb3_All : ∀ k < 300, qb3 k = true :=
  forall_of_chunks 60 5 _ fun c hc => by
    interval_cases c
    · exact qb3_0
    · exact qb3_1
    · exact qb3_2
    · exact qb3_3
    · exact qb3_4

theorem qpart3a : CFSG.KC.LQT.P.allN 2 (fun k => memK 300 C3P.F (QG k)) = true := by quickRfl

theorem qpart3 : j2FiveQPart 300 (j2FiveCCert 3) j2FiveQCert = true := by
  simp only [j2FiveQPart, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hQG k hk, any_eqA_unpack' hw bC3.1 bC3.2.1 pC3 (pQG k hk)]
    exact (allN_iff _ _).1 qpart3a k hk
  · rw [allLt_iff]
    intro k hk
    rw [bC3.2.1 k hk, hQG 0 (by norm_num), hQG 1 (by norm_num),
      comm_eq (pC3 k hk) (pQG 0 (by norm_num)), comm_eq (pC3 k hk) (pQG 1 (by norm_num)),
      any_eqA_unpack' hw bQ.1 bQ.2.1 pQ (pC3 k hk)]
    exact qb3_All k hk

theorem d3a : CFSG.KC.LQT.P.allN 2 (fun k => memK 300 C3P.F (DGP3 k)) = true := by quickRfl

theorem d3b : CFSG.KC.LQT.P.allN 2 (fun k => Nat.beq (Nat.shiftRight (DGP3 k) (315 * 9)) 0 &&
    sP (DGP3 k)) = true := by quickRfl

theorem d3c : CFSG.KC.LQT.P.allN 2 (fun k => CFSG.KC.LQT.P.allN 2 fun l =>
    memK 60 D3P.F (cj (CGP3 k) (DGP3 l))) = true := by quickRfl

theorem d3d : CFSG.KC.LQT.P.anyN 2 (fun k => CFSG.KC.LQT.P.anyN 2 fun l =>
    !(Nat.beq (cm (DGP3 k) (DGP3 l)) (cm (DGP3 l) (DGP3 k)))) = true := by quickRfl

@[expose] noncomputable def wd3 (k : ℕ) : Bool :=
  Nat.beq (D3P.F k) I || ((j2FiveSimpSel 3 k).all (fun j => decide (j < 60)) &&
    Nat.beq (j2FiveSimpW 3 k).length 2 && CFSG.KC.LQT.P.allN 2 fun l =>
      lettersOK (j2FiveSimpSel 3 k).length (j2FiveSimpW 3 k)[l]! &&
        Nat.beq (DGP3 l) (wordK 315 9 (mask 9) (pidn 315 9) (selC D3P.F k (j2FiveSimpSel 3 k))
          (selCI D3P.F k (j2FiveSimpSel 3 k)) (j2FiveSimpW 3 k)[l]!))

theorem wd3_0 : allR 0 30 wd3 = true := by quickRfl
theorem wd3_1 : allR 30 30 wd3 = true := by quickRfl

theorem words3 : conjWordsOK 315 (j2FiveDCert 3) (j2FiveDG 3) (j2FiveSimpSel 3)
    (j2FiveSimpW 3) = true := by
  have hs : (j2FiveDG 3).size = 2 := by decide
  have hall : ∀ k < 60, wd3 k = true := forall_of_chunks 30 2 _ fun c hc => by
    interval_cases c
    · exact wd3_0
    · exact wd3_1
  rw [conjWordsOK, bD3.1, allLt_iff]
  intro k hk
  have h := hall k hk
  rw [wd3, Bool.or_eq_true] at h
  rw [Bool.or_eq_true, bD3.2.1 k hk, hI, eqA_unpack' hw (pD3 k hk) pI]
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
  have hcs := conjSel_get bD3.1 bD3.2.1 pD3 hk hsel
  refine ⟨hlet, ?_⟩
  rw [hDG3 l (by rw [hs]; exact hl), wordA_unpack hw (fun h hh => (hcs h hh).1)
    (fun h hh => (hcs h hh).2.1) (fun h hh => (hcs h hh).2.2.1) (fun h hh => (hcs h hh).2.2.2)
    hlet, eqA_unpack' hw (pDG3 l hl) (permB_wordK hw (fun h hh => (hcs h hh).2.2.1)
      (fun h hh => (hcs h hh).2.2.2) hlet)]
  exact heq

@[expose] noncomputable def cd3 (k : ℕ) : Bool :=
  !(CFSG.KC.LQT.P.allN 2 fun l => Nat.beq (cm (C3P.F k) (DGP3 l)) (cm (DGP3 l) (C3P.F k))) ||
    CFSG.KC.LQT.P.anyN 5 fun e => Nat.beq (C3P.F k) (pw (LX 3) e)

theorem cd3_0 : allR 0 60 cd3 = true := by quickRfl
theorem cd3_1 : allR 60 60 cd3 = true := by quickRfl
theorem cd3_2 : allR 120 60 cd3 = true := by quickRfl
theorem cd3_3 : allR 180 60 cd3 = true := by quickRfl
theorem cd3_4 : allR 240 60 cd3 = true := by quickRfl

theorem cd3_All : ∀ k < 300, cd3 k = true :=
  forall_of_chunks 60 5 _ fun c hc => by
    interval_cases c
    · exact cd3_0
    · exact cd3_1
    · exact cd3_2
    · exact cd3_3
    · exact cd3_4

theorem bad3 : j2FiveBadCheck 3 (j2FiveCCert 3) (j2FiveDCert 3) j2FiveQCert = true := by
  have hs : (j2FiveDG 3).size = 2 := by decide
  have hcs : (j2FiveCG 3).size = 2 := by decide
  simp only [j2FiveBadCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨cpart3, qpart3⟩, enumD3⟩, bD3.1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, words3⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hDG3 k hk, any_eqA_unpack' hw bC3.1 bC3.2.1 pC3 (pDG3 k (by rw [← hs]; exact hk))]
    exact (allN_iff _ _).1 d3a k (by rw [← hs]; exact hk)
  · rw [allLt_iff]
    intro k hk
    have h := (allN_iff _ _).1 d3b k (by rw [← hs]; exact hk)
    rw [Bool.and_eq_true] at h
    rw [hDG3 k hk]
    exact inP_of h.1 (range_of_permOK (pDG3 k (by rw [← hs]; exact hk))) h.2
  · rw [allLt_iff]
    intro k hk
    rw [allLt_iff]
    intro l hl
    rw [hCG3 k hk, hDG3 l hl, conj_eq (pCG3 k (by rw [← hcs]; exact hk))
      (pDG3 l (by rw [← hs]; exact hl)), any_eqA_unpack' hw bD3.1 bD3.2.1 pD3
      (pCj (pCG3 k (by rw [← hcs]; exact hk)) (pDG3 l (by rw [← hs]; exact hl)))]
    exact (allN_iff _ _).1 ((allN_iff _ _).1 d3c k (by rw [← hcs]; exact hk)) l
      (by rw [← hs]; exact hl)
  · obtain ⟨k, hk, h⟩ := (anyN_iff _ _).1 d3d
    obtain ⟨l, hl, h⟩ := (anyN_iff _ _).1 h
    refine List.any_eq_true.2 ⟨k, List.mem_range.2 (by rw [hs]; exact hk), List.any_eq_true.2
      ⟨l, List.mem_range.2 (by rw [hs]; exact hl), ?_⟩⟩
    rw [hDG3 k (by rw [hs]; exact hk), hDG3 l (by rw [hs]; exact hl),
      comm_eq (pDG3 k hk) (pDG3 l hl)]
    exact h
  · rw [allLt_iff]
    intro k hk
    have h := cd3_All k hk
    rw [cd3, Bool.or_eq_true] at h
    rw [Bool.or_eq_true, bC3.2.1 k hk]
    rcases h with h | h
    · left
      rw [Bool.not_eq_true'] at h ⊢
      rw [Bool.eq_false_iff] at h ⊢
      intro h2
      apply h
      rw [allN_iff]
      intro l hl
      have h3 := allLt_iff.1 h2 l (by rw [hs]; exact hl)
      rw [hDG3 l (by rw [hs]; exact hl), comm_eq (pC3 k hk) (pDG3 l hl)] at h3
      exact h3
    · right
      obtain ⟨e, he, h⟩ := (anyN_iff _ _).1 h
      refine List.any_eq_true.2 ⟨e, List.mem_range.2 he, ?_⟩
      rw [hLX 3 (by norm_num), pow_eq (pLX 3 (by norm_num)),
        eqA_unpack' hw (pC3 k hk) (pPw (pLX 3 (by norm_num)) e)]
      exact h

end CertificateChecks.KernelMisc.J2F

end
