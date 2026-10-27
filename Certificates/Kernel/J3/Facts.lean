module

public import Certificates.Data.Kernel.LceSTab
public import Certificates.Data.Kernel.LceSHeRu
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Route
import Certificates.Kernel.LceSTab.Assemble
import Certificates.Kernel.HeRu.Assemble
import Certificates.Kernel.J3.Assemble
import Certificates.Kernel.J3.Labs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Checks.T_H_0
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Checks.T_W_0
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Checks.T_C_0
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Checks.T_L
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Checks.B_H_0
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Checks.B
import Certificates.Kernel.LceSTab.Chain

public section

namespace CertificateChecks.KernelJ3

open CFSG.KC CFSG.KC.LceS

theorem T.hints : CFSG.KC.Bind.hintsOK CFSG.KD.J3AT.selWT (nat_lit 256) (nat_lit 8) (nat_lit 2)
    CFSG.KD.J3AT.HS = true := by quickRfl

theorem T.per : CFSG.Certificates.LCE.wtPer CFSG.KD.J3AT.selWT (nat_lit 256) = true := by
  quickRfl

theorem T.norm : CFSG.Certificates.LCE.relsNorm CFSG.KD.J3AT.selRT (nat_lit 8) = true := by
  quickRfl

#lces_join CertificateChecks.KernelJ3.T.facts CFSG.KD.J3AT.sW 0 22
#lces_join CertificateChecks.KernelJ3.T.cover CFSG.KD.J3AT.sC 0 5
#lces_ok CertificateChecks.KernelJ3.T.ok CFSG.KD.J3AT.sH1 CFSG.KD.J3AT.sH0
  CertificateChecks.KernelJ3.T.hints CFSG.KD.J3AT.sH2 CFSG.KD.J3AT.sH3
  CertificateChecks.KernelJ3.T.per CertificateChecks.KernelJ3.T.norm
  CertificateChecks.KernelJ3.T.facts CertificateChecks.KernelJ3.T.cover

#labs_ok CertificateChecks.KernelJ3.TL.labsWF CFSG.KD.J3AT.LB 39270 1024

#labF_ok2 CertificateChecks.KernelJ3.TL.ok CFSG.KD.J3AT 8 2 CertificateChecks.KernelJ3.TL.labsWF

theorem B.hints : CFSG.KC.Bind.hintsOK CFSG.KD.J3AB.selWT (nat_lit 512) (nat_lit 30) (nat_lit 1)
    CFSG.KD.J3AB.HS = true := by quickRfl

theorem B.per : CFSG.Certificates.LCE.wtPer CFSG.KD.J3AB.selWT (nat_lit 512) = true := by
  quickRfl

theorem B.norm : CFSG.Certificates.LCE.relsNorm CFSG.KD.J3AB.selRT (nat_lit 30) = true := by
  quickRfl

theorem B.facts : Nat.beq (runFacts CFSG.KD.J3AB.blk CFSG.KD.J3AB.selWT CFSG.KD.J3AB.INV
    CFSG.KD.J3AB.nC (nat_lit 4)
    (CFSG.KC.LceSeg.seg CFSG.KD.J3AB.JF (Nat.sub (CFSG.KD.J3AB.loF 24) (CFSG.KD.J3AB.loF 0))
      (CFSG.KD.J3AB.loF 0)) (CFSG.KD.J3AB.accF 0)) (CFSG.KD.J3AB.accF 24) = true :=
  CFSG.KC.LceSeg.facts_chain _ _ _ _ _ _ _ _ 24 CFSG.KD.J3AB.okW_all

theorem B.cover : Nat.beq (runCover CFSG.KD.J3AB.blk CFSG.KD.J3AB.LVs (nat_lit 34242) (nat_lit 4)
    (CFSG.KC.LceSeg.seg CFSG.KD.J3AB.JV (Nat.sub (CFSG.KD.J3AB.loC 4) (CFSG.KD.J3AB.loC 0))
      (CFSG.KD.J3AB.loC 0)) (CFSG.KD.J3AB.accC 0)) (CFSG.KD.J3AB.accC 4) = true :=
  CFSG.KC.LceSeg.cover_chain _ _ _ _ _ _ _ 4 CFSG.KD.J3AB.okC_all
#lces_ok CertificateChecks.KernelJ3.B.ok CFSG.KD.J3AB.sH1 CFSG.KD.J3AB.sH0
  CertificateChecks.KernelJ3.B.hints CFSG.KD.J3AB.sH2 CFSG.KD.J3AB.sH3
  CertificateChecks.KernelJ3.B.per CertificateChecks.KernelJ3.B.norm
  CertificateChecks.KernelJ3.B.facts CertificateChecks.KernelJ3.B.cover

end CertificateChecks.KernelJ3

end
