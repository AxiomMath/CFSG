module

public import Certificates.Data.Kernel.LceSTab
public import CFSG.Certificates.Kernel.Common.LceSRange
public import CFSG.Certificates.Kernel.McL.RangeX
public import CFSG.Certificates.Kernel.McL.Rels
public import CFSG.Certificates.Kernel.McL.TC
public import CFSG.Certificates.Kernel.McL.Dce
public import CFSG.Certificates.Kernel.McL.Model
public import CFSG.Certificates.Kernel.McL.Lab
public import CFSG.Certificates.Kernel.McL.Data.A1
public import CFSG.Certificates.Kernel.McL.Data.A2
public import CFSG.Certificates.Kernel.McL.Data.A3
public import CFSG.Certificates.Kernel.McL.Data.A4
public import CFSG.Certificates.Kernel.McL.Data.A5
public import CFSG.Certificates.Kernel.McL.Data.AI
public import CFSG.Certificates.Kernel.McL.Data.AM
public import CFSG.Certificates.Kernel.McL.Data.AS
public import CFSG.Certificates.Kernel.McL.Data.BI
public import CFSG.Certificates.Kernel.McL.Data.BM
public import CFSG.Certificates.Kernel.McL.Data.BR
public import CFSG.Certificates.Kernel.McL.Data.CN
public import CFSG.Certificates.Kernel.McL.Data.CQ
public import CFSG.Certificates.Kernel.McL.Data.D
public import CFSG.Certificates.Kernel.McL.Data.M
public import CFSG.Certificates.Kernel.McL.Checks.A1
public import CFSG.Certificates.Kernel.McL.Checks.A2
public import CFSG.Certificates.Kernel.McL.Checks.A3
public import CFSG.Certificates.Kernel.McL.Checks.A4
public import CFSG.Certificates.Kernel.McL.Checks.A5
public import CFSG.Certificates.Kernel.McL.Checks.AI
public import CFSG.Certificates.Kernel.McL.Checks.AM
public import CFSG.Certificates.Kernel.McL.Checks.AS
public import CFSG.Certificates.Kernel.McL.Checks.BI
public import CFSG.Certificates.Kernel.McL.Checks.BM
public import CFSG.Certificates.Kernel.McL.Checks.BR
public import CFSG.Certificates.Kernel.McL.Checks.Bind
public import CFSG.Certificates.Kernel.McL.Checks.CN
public import CFSG.Certificates.Kernel.McL.Checks.CQC
public import CFSG.Certificates.Kernel.McL.Checks.CQH
public import CFSG.Certificates.Kernel.McL.Checks.CQW0
public import CFSG.Certificates.Kernel.McL.Checks.CQW1
public import CFSG.Certificates.Kernel.McL.Checks.CQW2
public import CFSG.Certificates.Kernel.McL.Checks.CQW3
public import CFSG.Certificates.Kernel.McL.Checks.D
public import CFSG.Certificates.Kernel.McL.Checks.M
import Certificates.Kernel.LceSTab.Assemble
import Certificates.Kernel.LceSTab.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMcL

open CFSG.KC CFSG.KC.LceS

theorem CQ.hints : CFSG.KC.Bind.hintsOK CFSG.KD.McL.CQ.selWT (nat_lit 2048) (nat_lit 78)
    (nat_lit 65536) CFSG.KD.McL.CQ.HS = true := by quickRfl

theorem CQ.per : CFSG.Certificates.LCE.wtPer CFSG.KD.McL.CQ.selWT (nat_lit 2048) = true := by
  quickRfl

theorem CQ.norm : CFSG.Certificates.LCE.relsNorm CFSG.KC.McL.Rels.QR (nat_lit 78) = true := by
  quickRfl

theorem CQ.nc : Nat.beq CFSG.KD.McL.CQ.nC CFSG.KD.McL.CQ.nC = true := by quickRfl

theorem CQ.facts : Nat.beq (runFacts CFSG.KD.McL.CQ.blk CFSG.KD.McL.CQ.selWT CFSG.KD.McL.CQ.INV
    CFSG.KD.McL.CQ.nC (nat_lit 6)
    (CFSG.KC.LceSeg.seg CFSG.KD.McL.CQ.JF
      (Nat.sub (CFSG.KD.McL.CQ.loF 873) (CFSG.KD.McL.CQ.loF 0)) (CFSG.KD.McL.CQ.loF 0))
    (CFSG.KD.McL.CQ.accF 0)) (CFSG.KD.McL.CQ.accF 873) = true :=
  CFSG.KC.LceSeg.facts_chain _ _ _ _ _ _ _ _ 873
    (CFSG.KC.LceSeg.forall_append 768 105 (CFSG.KC.LceSeg.forall_append 512 256
      (CFSG.KC.LceSeg.forall_append 256 256 CFSG.KD.McL.CQ.okW_0 CFSG.KD.McL.CQ.okW_1)
      CFSG.KD.McL.CQ.okW_2) CFSG.KD.McL.CQ.okW_3)

theorem CQ.cover : Nat.beq (runCover CFSG.KD.McL.CQ.blk CFSG.KD.McL.CQ.LVs CFSG.KD.McL.CQ.nF
    (nat_lit 6)
    (CFSG.KC.LceSeg.seg CFSG.KD.McL.CQ.JV
      (Nat.sub (CFSG.KD.McL.CQ.loC 102) (CFSG.KD.McL.CQ.loC 0)) (CFSG.KD.McL.CQ.loC 0))
    (CFSG.KD.McL.CQ.accC 0)) (CFSG.KD.McL.CQ.accC 102) = true :=
  CFSG.KC.LceSeg.cover_chain _ _ _ _ _ _ _ 102 CFSG.KD.McL.CQ.okC_all
#lces_ok CertificateChecks.KernelMcL.CQ.ok CFSG.KD.McL.CQ.sH1 CFSG.KD.McL.CQ.sH0
  CertificateChecks.KernelMcL.CQ.hints CFSG.KD.McL.CQ.sH2 CertificateChecks.KernelMcL.CQ.nc
  CertificateChecks.KernelMcL.CQ.per CertificateChecks.KernelMcL.CQ.norm
  CertificateChecks.KernelMcL.CQ.facts CertificateChecks.KernelMcL.CQ.cover

theorem CN.hints : CFSG.KC.Bind.hintsOK CFSG.KD.McL.CN.selWT (nat_lit 512) (nat_lit 79)
    (nat_lit 65536) CFSG.KD.McL.CN.HS = true := by quickRfl

theorem CN.per : CFSG.Certificates.LCE.wtPer CFSG.KD.McL.CN.selWT (nat_lit 512) = true := by
  quickRfl

theorem CN.norm : CFSG.Certificates.LCE.relsNorm CFSG.KC.McL.Rels.NR1 (nat_lit 79) = true := by
  quickRfl

theorem CN.nc : Nat.beq CFSG.KD.McL.CN.nC CFSG.KD.McL.CN.nC = true := by quickRfl

theorem CN.facts : Nat.beq (runFacts CFSG.KD.McL.CN.blk CFSG.KD.McL.CN.selWT CFSG.KD.McL.CN.INV
    CFSG.KD.McL.CN.nC (nat_lit 6)
    (CFSG.KC.LceSeg.seg CFSG.KD.McL.CN.JF
      (Nat.sub (CFSG.KD.McL.CN.loF 32) (CFSG.KD.McL.CN.loF 0)) (CFSG.KD.McL.CN.loF 0))
    (CFSG.KD.McL.CN.accF 0)) (CFSG.KD.McL.CN.accF 32) = true :=
  CFSG.KC.LceSeg.facts_chain _ _ _ _ _ _ _ _ 32 CFSG.KD.McL.CN.okW_all

theorem CN.cover : Nat.beq (runCover CFSG.KD.McL.CN.blk CFSG.KD.McL.CN.LVs CFSG.KD.McL.CN.nF
    (nat_lit 6)
    (CFSG.KC.LceSeg.seg CFSG.KD.McL.CN.JV
      (Nat.sub (CFSG.KD.McL.CN.loC 13) (CFSG.KD.McL.CN.loC 0)) (CFSG.KD.McL.CN.loC 0))
    (CFSG.KD.McL.CN.accC 0)) (CFSG.KD.McL.CN.accC 13) = true :=
  CFSG.KC.LceSeg.cover_chain _ _ _ _ _ _ _ 13 CFSG.KD.McL.CN.okC_all
#lces_ok CertificateChecks.KernelMcL.CN.ok CFSG.KD.McL.CN.sH1 CFSG.KD.McL.CN.sH0
  CertificateChecks.KernelMcL.CN.hints CFSG.KD.McL.CN.sH2 CertificateChecks.KernelMcL.CN.nc
  CertificateChecks.KernelMcL.CN.per CertificateChecks.KernelMcL.CN.norm
  CertificateChecks.KernelMcL.CN.facts CertificateChecks.KernelMcL.CN.cover

theorem small_XT : CFSG.KC.McL.RangeX.smallTabB CFSG.KC.McL.Rels.XT = true := by quickRfl

theorem lt_XT : CFSG.KC.McL.RangeX.xtLt CFSG.KC.McL.Rels.XT = true := by quickRfl
theorem small_XD : CFSG.KC.McL.RangeX.smallTabB CFSG.KC.McL.Rels.XD = true := by quickRfl

theorem let_NR1 : CFSG.KC.McL.RangeX.entsBelow CFSG.KC.McL.Rels.NR1 (nat_lit 79) (nat_lit 6) =
    true := by quickRfl
theorem let_KS : CFSG.KC.McL.RangeX.entsBelow CFSG.KC.McL.Rels.KS (nat_lit 3) (nat_lit 6) =
    true := by quickRfl
theorem let_KQ : CFSG.KC.McL.RangeX.entsBelow CFSG.KC.McL.Rels.KQ (nat_lit 3) (nat_lit 6) =
    true := by quickRfl
theorem let_BM : CFSG.KC.McL.RangeX.entsBelow CFSG.KD.McL.BM.SN CFSG.KD.McL.BM.K (nat_lit 6) =
    true := by quickRfl
theorem let_BI : CFSG.KC.McL.RangeX.entsBelow CFSG.KD.McL.BI.SN CFSG.KD.McL.BI.K (nat_lit 6) =
    true := by quickRfl
theorem let_BR : CFSG.KC.McL.RangeX.entsBelow CFSG.KD.McL.BR.SN CFSG.KD.McL.BR.K (nat_lit 6) =
    true := by quickRfl

@[expose] noncomputable def trw (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) CFSG.KD.McL.D.TRW1 CFSG.KD.McL.D.TRW0 (Nat.beq k (nat_lit 0))

theorem let_TRW : CFSG.KC.McL.RangeX.entsBelow trw (nat_lit 2) (nat_lit 4) = true := by quickRfl

theorem ep_M : CFSG.KC.McL.RangeX.epWrap CFSG.KD.McL.M.EP CFSG.KD.McL.M.ED CFSG.KD.McL.M.nE
    (nat_lit 128) = true := by quickRfl

theorem norm_TC : CFSG.Certificates.LCE.relsNorm CFSG.KC.McL.TC.sel (nat_lit 15) = true := by
  quickRfl
theorem norm_GR : CFSG.Certificates.LCE.relsNorm CFSG.KC.McL.Rels.GR (nat_lit 34) = true := by
  quickRfl
theorem norm_STBM : CFSG.Certificates.LCE.relsNorm CFSG.KD.McL.BM.ST CFSG.KD.McL.BM.K = true := by
  quickRfl
theorem norm_STBI : CFSG.Certificates.LCE.relsNorm CFSG.KD.McL.BI.ST CFSG.KD.McL.BI.K = true := by
  quickRfl
theorem norm_STBR : CFSG.Certificates.LCE.relsNorm CFSG.KD.McL.BR.ST CFSG.KD.McL.BR.K = true := by
  quickRfl

theorem per_A1 : CFSG.KC.LceSR.wtPer0 CFSG.KD.McL.A1.WT CFSG.KD.McL.A1.nW (nat_lit 8) = true := by
  quickRfl
theorem per_A2 : CFSG.KC.LceSR.wtPer0 CFSG.KD.McL.A2.WT CFSG.KD.McL.A2.nW (nat_lit 8) = true := by
  quickRfl
theorem per_A3 : CFSG.KC.LceSR.wtPer0 CFSG.KD.McL.A3.WT CFSG.KD.McL.A3.nW (nat_lit 32) = true := by
  quickRfl
theorem per_A4 : CFSG.KC.LceSR.wtPer0 CFSG.KD.McL.A4.WT CFSG.KD.McL.A4.nW (nat_lit 16) = true := by
  quickRfl
theorem per_A5 : CFSG.KC.LceSR.wtPer0 CFSG.KD.McL.A5.WT CFSG.KD.McL.A5.nW (nat_lit 32) = true := by
  quickRfl
theorem per_AI : CFSG.KC.LceSR.wtPer0 CFSG.KD.McL.AI.WT CFSG.KD.McL.AI.nW (nat_lit 32) = true := by
  quickRfl
theorem per_AM : CFSG.KC.LceSR.wtPer0 CFSG.KD.McL.AM.WT CFSG.KD.McL.AM.nW (nat_lit 8) = true := by
  quickRfl
theorem per_AS : CFSG.KC.LceSR.wtPer0 CFSG.KD.McL.AS.WT CFSG.KD.McL.AS.nW (nat_lit 16) = true := by
  quickRfl
theorem per_BI : CFSG.KC.LceSR.wtPer0 CFSG.KD.McL.BI.WT CFSG.KD.McL.BI.nW (nat_lit 16) = true := by
  quickRfl
theorem per_BM : CFSG.KC.LceSR.wtPer0 CFSG.KD.McL.BM.WT CFSG.KD.McL.BM.nW (nat_lit 64) = true := by
  quickRfl
theorem per_BR : CFSG.KC.LceSR.wtPer0 CFSG.KD.McL.BR.WT CFSG.KD.McL.BR.nW (nat_lit 256) = true := by
  quickRfl

end CertificateChecks.KernelMcL

end
