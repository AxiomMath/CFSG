module

public import Certificates.Data.Kernel.LceSTab
public import CFSG.Certificates.Kernel.J4.M24Data.M24B_Sel
public import Certificates.Kernel.LceSTab.Chain
import Certificates.Kernel.LceSTab.Assemble
import CFSG.Certificates.Kernel.J4.M24Checks.M24RG
public import CFSG.Certificates.Kernel.J4.M24Checks.TH
public import CFSG.Certificates.Kernel.J4.M24Checks.TW0
public import CFSG.Certificates.Kernel.J4.M24Checks.TW1
public import CFSG.Certificates.Kernel.J4.M24Checks.TW2
public import CFSG.Certificates.Kernel.J4.M24Checks.TW3
public import CFSG.Certificates.Kernel.J4.M24Checks.TW4
public import CFSG.Certificates.Kernel.J4.M24Checks.TW5
public import CFSG.Certificates.Kernel.J4.M24Checks.TW6
public import CFSG.Certificates.Kernel.J4.M24Checks.TW7
public import CFSG.Certificates.Kernel.J4.M24Checks.TW8
public import CFSG.Certificates.Kernel.J4.M24Checks.TW9
public import CFSG.Certificates.Kernel.J4.M24Checks.TW10
public import CFSG.Certificates.Kernel.J4.M24Checks.TC0
public import CFSG.Certificates.Kernel.J4.M24Checks.TC1
public import CFSG.Certificates.Kernel.J4.M24Checks.TC2
public import CFSG.Certificates.Kernel.J4.M24Checks.TC3

public section

namespace CertificateChecks.KernelBounds.M24

open CFSG.KC CFSG.KC.LceS CFSG.KC.LceSeg

theorem allW : ∀ i < 2643, CFSG.KD.M24B.okW i = true :=
  forall_append 2560 83 (forall_append 2304 256 (forall_append 2048 256 (forall_append 1792 256
    (forall_append 1536 256 (forall_append 1280 256 (forall_append 1024 256 (forall_append 768 256
      (forall_append 512 256 (forall_append 256 256 CFSG.KD.M24B.okW_0 CFSG.KD.M24B.okW_1)
        CFSG.KD.M24B.okW_2) CFSG.KD.M24B.okW_3) CFSG.KD.M24B.okW_4) CFSG.KD.M24B.okW_5)
    CFSG.KD.M24B.okW_6) CFSG.KD.M24B.okW_7) CFSG.KD.M24B.okW_8) CFSG.KD.M24B.okW_9)
    CFSG.KD.M24B.okW_10

theorem allC : ∀ i < 799, CFSG.KD.M24B.okC i = true :=
  forall_append 768 31 (forall_append 512 256 (forall_append 256 256 CFSG.KD.M24B.okC_0
    CFSG.KD.M24B.okC_1) CFSG.KD.M24B.okC_2) CFSG.KD.M24B.okC_3

theorem facts : Nat.beq (runFacts CFSG.KD.M24B.blk CFSG.KD.M24B.selWT CFSG.KD.M24B.INV
    CFSG.KD.M24B.nC (nat_lit 14)
    (seg CFSG.KD.M24B.JF (Nat.sub (CFSG.KD.M24B.loF 2643) (CFSG.KD.M24B.loF 0))
      (CFSG.KD.M24B.loF 0)) (CFSG.KD.M24B.accF 0)) (CFSG.KD.M24B.accF 2643) = true :=
  facts_chain _ _ _ _ _ _ _ _ 2643 allW

theorem cover : Nat.beq (runCover CFSG.KD.M24B.blk CFSG.KD.M24B.LVs (nat_lit 3848842)
    (nat_lit 14)
    (seg CFSG.KD.M24B.JV (Nat.sub (CFSG.KD.M24B.loC 799) (CFSG.KD.M24B.loC 0))
      (CFSG.KD.M24B.loC 0)) (CFSG.KD.M24B.accC 0)) (CFSG.KD.M24B.accC 799) = true :=
  cover_chain _ _ _ _ _ _ _ 799 allC

end CertificateChecks.KernelBounds.M24

#lces_ok CertificateChecks.KernelBounds.M24.lce_ok CFSG.KD.M24B.sH1 CFSG.KD.M24B.sH0
  CFSG.KD.M24B.hints CFSG.KD.M24B.sH2 CFSG.KD.M24B.sH3 CFSG.KJ4.M24G.wt_per
  CFSG.KJ4.M24G.rels_norm CertificateChecks.KernelBounds.M24.facts
  CertificateChecks.KernelBounds.M24.cover

end
