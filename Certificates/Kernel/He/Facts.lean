module

public import Certificates.Data.Kernel.LceSTab
public import Certificates.Data.Kernel.LceSHeRu
public import CFSG.Certificates.Kernel.He.Bound.Route
import Certificates.Kernel.LceSTab.Assemble
import Certificates.Kernel.HeRu.Assemble
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.LceSTab.Chain
public import CFSG.Certificates.Kernel.He.Bound.Checks.PH
public import CFSG.Certificates.Kernel.He.Bound.Checks.PW0
public import CFSG.Certificates.Kernel.He.Bound.Checks.PW1
public import CFSG.Certificates.Kernel.He.Bound.Checks.PW2
public import CFSG.Certificates.Kernel.He.Bound.Checks.PW3
public import CFSG.Certificates.Kernel.He.Bound.Checks.PW4
public import CFSG.Certificates.Kernel.He.Bound.Checks.PC0
public import CFSG.Certificates.Kernel.He.Bound.Checks.PC1
public import CFSG.Certificates.Kernel.He.Bound.Checks.C_H_0
public import CFSG.Certificates.Kernel.He.Bound.Checks.C_W_0
public import CFSG.Certificates.Kernel.He.Bound.Checks.C_L
public import CFSG.Certificates.Kernel.He.Bound.Checks.Q

public section

namespace CertificateChecks.KernelHe

open CFSG.KC CFSG.KC.LceS

theorem P.hints : CFSG.KC.Bind.hintsOK CFSG.KD.HeBP.selWT (nat_lit 2048) (nat_lit 7) (nat_lit 2)
    CFSG.KD.HeBP.HS = true := by quickRfl

theorem P.per : CFSG.Certificates.LCE.wtPer CFSG.KD.HeBP.selWT (nat_lit 2048) = true := by
  quickRfl

theorem P.norm : CFSG.Certificates.LCE.relsNorm CFSG.KD.HeBP.selRT (nat_lit 7) = true := by
  quickRfl

theorem P.facts : Nat.beq (runFacts CFSG.KD.HeBP.blk CFSG.KD.HeBP.selWT CFSG.KD.HeBP.INV
    CFSG.KD.HeBP.nC (nat_lit 4)
    (CFSG.KC.LceSeg.seg CFSG.KD.HeBP.JF (Nat.sub (CFSG.KD.HeBP.loF 1131) (CFSG.KD.HeBP.loF 0))
      (CFSG.KD.HeBP.loF 0)) (CFSG.KD.HeBP.accF 0)) (CFSG.KD.HeBP.accF 1131) = true :=
  CFSG.KC.LceSeg.facts_chain _ _ _ _ _ _ _ _ 1131
    (CFSG.KC.LceSeg.forall_append 1024 107 (CFSG.KC.LceSeg.forall_append 768 256
      (CFSG.KC.LceSeg.forall_append 512 256 (CFSG.KC.LceSeg.forall_append 256 256
        CFSG.KD.HeBP.okW_0 CFSG.KD.HeBP.okW_1) CFSG.KD.HeBP.okW_2) CFSG.KD.HeBP.okW_3)
      CFSG.KD.HeBP.okW_4)

theorem P.cover : Nat.beq (runCover CFSG.KD.HeBP.blk CFSG.KD.HeBP.LVs (nat_lit 1157714) (nat_lit 4)
    (CFSG.KC.LceSeg.seg CFSG.KD.HeBP.JV (Nat.sub (CFSG.KD.HeBP.loC 271) (CFSG.KD.HeBP.loC 0))
      (CFSG.KD.HeBP.loC 0)) (CFSG.KD.HeBP.accC 0)) (CFSG.KD.HeBP.accC 271) = true :=
  CFSG.KC.LceSeg.cover_chain _ _ _ _ _ _ _ 271
    (CFSG.KC.LceSeg.forall_append 256 15 CFSG.KD.HeBP.okC_0 CFSG.KD.HeBP.okC_1)

#lces_ok CertificateChecks.KernelHe.P.ok CFSG.KD.HeBP.sH1 CFSG.KD.HeBP.sH0
  CertificateChecks.KernelHe.P.hints CFSG.KD.HeBP.sH2 CFSG.KD.HeBP.sH3
  CertificateChecks.KernelHe.P.per
  CertificateChecks.KernelHe.P.norm CertificateChecks.KernelHe.P.facts
  CertificateChecks.KernelHe.P.cover

theorem Q.hints : CFSG.KC.Bind.hintsOK CFSG.KD.HeBQ.selWT (nat_lit 512) (nat_lit 6) (nat_lit 1)
    CFSG.KD.HeBQ.HS = true := by quickRfl

theorem Q.per : CFSG.Certificates.LCE.wtPer CFSG.KD.HeBQ.selWT (nat_lit 512) = true := by
  quickRfl

theorem Q.norm : CFSG.Certificates.LCE.relsNorm CFSG.KD.HeBQ.selRT (nat_lit 6) = true := by
  quickRfl

theorem Q.facts : Nat.beq (runFacts CFSG.KD.HeBQ.blk CFSG.KD.HeBQ.selWT CFSG.KD.HeBQ.INV
    CFSG.KD.HeBQ.nC (nat_lit 4)
    (CFSG.KC.LceSeg.seg CFSG.KD.HeBQ.JF (Nat.sub (CFSG.KD.HeBQ.loF 38) (CFSG.KD.HeBQ.loF 0))
      (CFSG.KD.HeBQ.loF 0)) (CFSG.KD.HeBQ.accF 0)) (CFSG.KD.HeBQ.accF 38) = true :=
  CFSG.KC.LceSeg.facts_chain _ _ _ _ _ _ _ _ 38 CFSG.KD.HeBQ.okW_all

theorem Q.cover : Nat.beq (runCover CFSG.KD.HeBQ.blk CFSG.KD.HeBQ.LVs (nat_lit 46669) (nat_lit 4)
    (CFSG.KC.LceSeg.seg CFSG.KD.HeBQ.JV (Nat.sub (CFSG.KD.HeBQ.loC 4) (CFSG.KD.HeBQ.loC 0))
      (CFSG.KD.HeBQ.loC 0)) (CFSG.KD.HeBQ.accC 0)) (CFSG.KD.HeBQ.accC 4) = true :=
  CFSG.KC.LceSeg.cover_chain _ _ _ _ _ _ _ 4 CFSG.KD.HeBQ.okC_all

#lces_ok CertificateChecks.KernelHe.Q.ok CFSG.KD.HeBQ.sH1 CFSG.KD.HeBQ.sH0
  CertificateChecks.KernelHe.Q.hints CFSG.KD.HeBQ.sH2 CFSG.KD.HeBQ.sH3
  CertificateChecks.KernelHe.Q.per
  CertificateChecks.KernelHe.Q.norm CertificateChecks.KernelHe.Q.facts
  CertificateChecks.KernelHe.Q.cover

#lab_ok He CertificateChecks.KernelHe.C.ok CFSG.KD.HeBC

end CertificateChecks.KernelHe

end
