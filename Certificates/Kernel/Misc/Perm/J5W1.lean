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

theorem pCG1 : ∀ k < 2, permB 315 9 (CGP1 k) = true := (allN_iff _ _).1 (by quickRfl)

theorem cpart1 : j2FiveCPart 1 50 (j2FiveCCert 1) = true := by
  have hs : (j2FiveCG 1).size = 2 := by decide
  simp only [j2FiveCPart, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨enumC1, bC1.1⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hCG1 k hk, hLX 1 (by norm_num)]
    rw [hs] at hk
    interval_cases k <;> exact comm_of (by quickRfl) (pLX 1 (by norm_num)) (by quickRfl)
  · rw [allLt_iff]
    intro k hk
    rw [hCG1 k hk]
    rw [hs] at hk
    interval_cases k <;> exact inR_of (by quickRfl) (by quickRfl)

theorem qpart1a : CFSG.KC.LQT.P.allN 2 (fun k => memK 50 C1P.F (QG k)) = true := by quickRfl

theorem qpart1b : CFSG.KC.LQT.P.allN 50 (fun k =>
    !(Nat.beq (cm (C1P.F k) (QG 0)) (cm (QG 0) (C1P.F k)) &&
      Nat.beq (cm (C1P.F k) (QG 1)) (cm (QG 1) (C1P.F k))) || memK 25 QP.F (C1P.F k)) = true := by
  quickRfl

theorem qpart1 : j2FiveQPart 50 (j2FiveCCert 1) j2FiveQCert = true := by
  simp only [j2FiveQPart, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [hQG k hk, any_eqA_unpack' hw bC1.1 bC1.2.1 pC1 (pQG k hk)]
    exact (allN_iff _ _).1 qpart1a k hk
  · rw [allLt_iff]
    intro k hk
    rw [bC1.2.1 k hk, hQG 0 (by norm_num), hQG 1 (by norm_num),
      comm_eq (pC1 k hk) (pQG 0 (by norm_num)), comm_eq (pC1 k hk) (pQG 1 (by norm_num)),
      any_eqA_unpack' hw bQ.1 bQ.2.1 pQ (pC1 k hk)]
    exact (allN_iff _ _).1 qpart1b k hk

theorem good1c : CFSG.KC.LQT.P.allN 2 (fun k => CFSG.KC.LQT.P.allN 2 fun l =>
    memK 25 QP.F (cj (CGP1 k) (QG l))) = true := by quickRfl

theorem good1 : j2FiveGoodCheck 1 (j2FiveCCert 1) j2FiveQCert = true := by
  have hs : (j2FiveCG 1).size = 2 := by decide
  simp only [j2FiveGoodCheck, Bool.and_eq_true]
  refine ⟨⟨cpart1, qpart1⟩, ?_⟩
  rw [allLt_iff]
  intro k hk
  rw [allLt_iff]
  intro l hl
  rw [hCG1 k hk, hQG l hl]
  rw [hs] at hk
  rw [conj_eq (pCG1 k hk) (pQG l hl),
    any_eqA_unpack' hw bQ.1 bQ.2.1 pQ (pCj (pCG1 k hk) (pQG l hl))]
  exact (allN_iff _ _).1 ((allN_iff _ _).1 good1c k hk) l hl

end CertificateChecks.KernelMisc.J2F

end
