module

public import Certificates.Kernel.Misc.Perm.J5H2
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.KC.Misc.Clos (allN_iff anyN_iff)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem pCG4 : ∀ k < 3, permB 315 9 (CGP4 k) = true := (allN_iff _ _).1 (by quickRfl)

theorem cpart4 : j2FiveCPart 4 50 (j2FiveCCert 4) = true := by
  have hs : (j2FiveCG 4).size = 3 := by decide
  simp only [j2FiveCPart, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨enumC4, bC4.1⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hCG4 k hk, hLX 4 (by norm_num)]
    rw [hs] at hk
    interval_cases k <;> exact comm_of (by quickRfl) (pLX 4 (by norm_num)) (by quickRfl)
  · rw [allLt_iff]
    intro k hk
    rw [hCG4 k hk]
    rw [hs] at hk
    interval_cases k <;> exact inR_of (by quickRfl) (by quickRfl)

theorem qpart4a : CFSG.KC.LQT.P.allN 2 (fun k => memK 50 C4P.F (QG k)) = true := by quickRfl

theorem qpart4b : CFSG.KC.LQT.P.allN 50 (fun k =>
    !(Nat.beq (cm (C4P.F k) (QG 0)) (cm (QG 0) (C4P.F k)) &&
      Nat.beq (cm (C4P.F k) (QG 1)) (cm (QG 1) (C4P.F k))) || memK 25 QP.F (C4P.F k)) = true := by
  quickRfl

theorem qpart4 : j2FiveQPart 50 (j2FiveCCert 4) j2FiveQCert = true := by
  simp only [j2FiveQPart, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hQG k hk, any_eqA_unpack' hw bC4.1 bC4.2.1 pC4 (pQG k hk)]
    exact (allN_iff _ _).1 qpart4a k hk
  · rw [allLt_iff]
    intro k hk
    rw [bC4.2.1 k hk, hQG 0 (by norm_num), hQG 1 (by norm_num),
      comm_eq (pC4 k hk) (pQG 0 (by norm_num)), comm_eq (pC4 k hk) (pQG 1 (by norm_num)),
      any_eqA_unpack' hw bQ.1 bQ.2.1 pQ (pC4 k hk)]
    exact (allN_iff _ _).1 qpart4b k hk

theorem good4c : CFSG.KC.LQT.P.allN 3 (fun k => CFSG.KC.LQT.P.allN 2 fun l =>
    memK 25 QP.F (cj (CGP4 k) (QG l))) = true := by quickRfl

theorem good4 : j2FiveGoodCheck 4 (j2FiveCCert 4) j2FiveQCert = true := by
  have hs : (j2FiveCG 4).size = 3 := by decide
  simp only [j2FiveGoodCheck, Bool.and_eq_true]
  refine ⟨⟨cpart4, qpart4⟩, ?_⟩
  rw [allLt_iff]
  intro k hk
  rw [allLt_iff]
  intro l hl
  rw [hCG4 k hk, hQG l hl]
  rw [hs] at hk
  rw [conj_eq (pCG4 k hk) (pQG l hl),
    any_eqA_unpack' hw bQ.1 bQ.2.1 pQ (pCj (pCG4 k hk) (pQG l hl))]
  exact (allN_iff _ _).1 ((allN_iff _ _).1 good4c k hk) l hl

end CertificateChecks.KernelMisc.J2F

end
