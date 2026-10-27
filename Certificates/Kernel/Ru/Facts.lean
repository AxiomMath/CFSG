module

public import Certificates.Data.Kernel.LceSTab
public import Certificates.Data.Kernel.LceSHeRu
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Route
import Certificates.Kernel.LceSTab.Assemble
import Certificates.Kernel.HeRu.Assemble
import Certificates.Kernel.Ru.WordsJoin
public import Certificates.Kernel.Ru.Words
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Ru.Bound.Checks.P_H_0
public import CFSG.Certificates.Kernel.Ru.Bound.Checks.P
import Certificates.Kernel.LceSTab.Chain
public import CFSG.Certificates.Kernel.Ru.Bound.Checks.C_H_0
public import CFSG.Certificates.Kernel.Ru.Bound.Checks.C_W_0
public import CFSG.Certificates.Kernel.Ru.Bound.Checks.A
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Checks.C_L
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Checks.M_H_0
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Checks.M_W_0
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Checks.M_C_0
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Checks.M_L
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Checks.B_H_0
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Checks.B

public section

namespace CertificateChecks.KernelRu

open CFSG.KC CFSG.KC.LceS

theorem P.hints : CFSG.KC.Bind.hintsOK CFSG.KD.RuBP.selWT (nat_lit 512) (nat_lit 12) (nat_lit 2)
    CFSG.KD.RuBP.HS = true := by quickRfl

theorem P.per : CFSG.Certificates.LCE.wtPer CFSG.KD.RuBP.selWT (nat_lit 512) = true := by
  quickRfl

theorem P.norm : CFSG.Certificates.LCE.relsNorm CFSG.KD.RuBP.selRT (nat_lit 12) = true := by
  quickRfl

theorem P.facts : Nat.beq (runFacts CFSG.KD.RuBP.blk CFSG.KD.RuBP.selWT CFSG.KD.RuBP.INV
    CFSG.KD.RuBP.nC (nat_lit 6)
    (CFSG.KC.LceSeg.seg CFSG.KD.RuBP.JF (Nat.sub (CFSG.KD.RuBP.loF 49) (CFSG.KD.RuBP.loF 0))
      (CFSG.KD.RuBP.loF 0)) (CFSG.KD.RuBP.accF 0)) (CFSG.KD.RuBP.accF 49) = true :=
  CFSG.KC.LceSeg.facts_chain _ _ _ _ _ _ _ _ 49 CFSG.KD.RuBP.okW_all

theorem P.cover : Nat.beq (runCover CFSG.KD.RuBP.blk CFSG.KD.RuBP.LVs (nat_lit 86823) (nat_lit 6)
    (CFSG.KC.LceSeg.seg CFSG.KD.RuBP.JV (Nat.sub (CFSG.KD.RuBP.loC 9) (CFSG.KD.RuBP.loC 0))
      (CFSG.KD.RuBP.loC 0)) (CFSG.KD.RuBP.accC 0)) (CFSG.KD.RuBP.accC 9) = true :=
  CFSG.KC.LceSeg.cover_chain _ _ _ _ _ _ _ 9 CFSG.KD.RuBP.okC_all
#lces_ok CertificateChecks.KernelRu.P.ok CFSG.KD.RuBP.sH1 CFSG.KD.RuBP.sH0
  CertificateChecks.KernelRu.P.hints CFSG.KD.RuBP.sH2 CFSG.KD.RuBP.sH3
  CertificateChecks.KernelRu.P.per CertificateChecks.KernelRu.P.norm
  CertificateChecks.KernelRu.P.facts CertificateChecks.KernelRu.P.cover

#lab_ok Ru CertificateChecks.KernelRu.C.ok CFSG.KD.RuBC

theorem M.hints : CFSG.KC.Bind.hintsOK CFSG.KD.RuBAM.selWT (nat_lit 256) (nat_lit 16) (nat_lit 10)
    CFSG.KD.RuBAM.HS = true := by quickRfl

theorem M.per : CFSG.Certificates.LCE.wtPer CFSG.KD.RuBAM.selWT (nat_lit 256) = true := by
  quickRfl

theorem M.norm : CFSG.Certificates.LCE.relsNorm CFSG.KD.RuBAM.selRT (nat_lit 16) = true := by
  quickRfl

#lces_join CertificateChecks.KernelRu.M.facts CFSG.KD.RuBAM.sW 0 4
#lces_join CertificateChecks.KernelRu.M.cover CFSG.KD.RuBAM.sC 0 1
#lces_ok CertificateChecks.KernelRu.M.ok CFSG.KD.RuBAM.sH1 CFSG.KD.RuBAM.sH0
  CertificateChecks.KernelRu.M.hints CFSG.KD.RuBAM.sH2 CFSG.KD.RuBAM.sH3
  CertificateChecks.KernelRu.M.per CertificateChecks.KernelRu.M.norm
  CertificateChecks.KernelRu.M.facts CertificateChecks.KernelRu.M.cover

#lab_ok LabF CertificateChecks.KernelRu.ML.ok CFSG.KD.RuBAM 16 10

#words_join CertificateChecks.KernelRu.B.words CFSG.KD.RuBAB 16 81 2

theorem B.per : CFSG.Certificates.LCE.wtPer CFSG.KD.RuBAB.selWT (nat_lit 8192) = true := by
  quickRfl

theorem B.norm : CFSG.Certificates.LCE.relsNorm CFSG.KD.RuBAB.selRT (nat_lit 81) = true := by
  quickRfl

theorem B.facts : Nat.beq (runFacts CFSG.KD.RuBAB.blk CFSG.KD.RuBAB.selWT CFSG.KD.RuBAB.INV
    CFSG.KD.RuBAB.nC (nat_lit 20)
    (CFSG.KC.LceSeg.seg CFSG.KD.RuBAB.JF (Nat.sub (CFSG.KD.RuBAB.loF 230) (CFSG.KD.RuBAB.loF 0))
      (CFSG.KD.RuBAB.loF 0)) (CFSG.KD.RuBAB.accF 0)) (CFSG.KD.RuBAB.accF 230) = true :=
  CFSG.KC.LceSeg.facts_chain _ _ _ _ _ _ _ _ 230 CFSG.KD.RuBAB.okW_all

theorem B.cover : Nat.beq (runCover CFSG.KD.RuBAB.blk CFSG.KD.RuBAB.LVs (nat_lit 415593)
    (nat_lit 20)
    (CFSG.KC.LceSeg.seg CFSG.KD.RuBAB.JV (Nat.sub (CFSG.KD.RuBAB.loC 24) (CFSG.KD.RuBAB.loC 0))
      (CFSG.KD.RuBAB.loC 0)) (CFSG.KD.RuBAB.accC 0)) (CFSG.KD.RuBAB.accC 24) = true :=
  CFSG.KC.LceSeg.cover_chain _ _ _ _ _ _ _ 24 CFSG.KD.RuBAB.okC_all
#lces_ok CertificateChecks.KernelRu.B.ok CFSG.KD.RuBAB.sH1 CertificateChecks.KernelRu.B.words
  CertificateChecks.KernelRu.B.words.hints CFSG.KD.RuBAB.sH2 CFSG.KD.RuBAB.sH3
  CertificateChecks.KernelRu.B.per CertificateChecks.KernelRu.B.norm
  CertificateChecks.KernelRu.B.facts CertificateChecks.KernelRu.B.cover

theorem A.per0 : CFSG.KC.LceSR.wtPer0 CFSG.KD.RuBA.WT CFSG.KD.RuBA.nW (nat_lit 64) = true := by
  quickRfl

@[expose] noncomputable def A.qOK (k : Nat) : Bool :=
  andB (Nat.beq (wLen (CFSG.KD.RuBA.TW k)) (wLen (CFSG.KD.RuBAM.selRT (Nat.add (nat_lit 7) k))))
    (qlet (wWord (CFSG.KD.RuBA.TW k)) (wWord (CFSG.KD.RuBAM.selRT (Nat.add (nat_lit 7) k)))
      (wLen (CFSG.KD.RuBAM.selRT (Nat.add (nat_lit 7) k))))

theorem A.q0 : A.qOK (nat_lit 0) = true := by quickRfl
theorem A.q1 : A.qOK (nat_lit 1) = true := by quickRfl
theorem A.q2 : A.qOK (nat_lit 2) = true := by quickRfl
theorem A.q3 : A.qOK (nat_lit 3) = true := by quickRfl
theorem A.q4 : A.qOK (nat_lit 4) = true := by quickRfl
theorem A.q5 : A.qOK (nat_lit 5) = true := by quickRfl
theorem A.q6 : A.qOK (nat_lit 6) = true := by quickRfl
theorem A.q7 : A.qOK (nat_lit 7) = true := by quickRfl
theorem A.q8 : A.qOK (nat_lit 8) = true := by quickRfl

end CertificateChecks.KernelRu

end
