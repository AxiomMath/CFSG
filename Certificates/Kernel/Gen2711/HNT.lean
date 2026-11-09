module

public import Certificates.Kernel.FusLay.HN
public import Certificates.Data.Kernel.OpsLayT
public import Certificates.Data.Inputs2711eHN
public import Certificates.Data.Kernel.GenWf
public import Certificates.Kernel.LocalComp.LaySnaps
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
meta import Certificates.Data.Inputs2711eHN
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

meta def CertificateChecks.KernelFusLay.HN.tProg : List CFSG.SectionRank.Native.Op :=
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e.hnGenData.prog

#lay_snaps CertificateChecks.KernelFusLay.HN.T 5 133 CertificateChecks.KernelFusLay.HN.A
  CertificateChecks.KernelFusLay.HN.B CertificateChecks.KernelFusLay.HN.tProg 619 100

public section

namespace CertificateChecks.KernelFusLay.HN

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.AlphaHN

@[expose] noncomputable def tCh (i : Nat) : Bool :=
  chunkL lay hnGenData.prog 100 i (T.SL.getD i []) (T.SL.getD (i + 1) [])

@[expose] noncomputable def tFa (i : Nat) : Bool :=
  factsL lay (T.SL.getD 17 []) hnGenData.nregs hnGenData.facts 8 i

theorem gen271104T_init : eqL (T.SL.getD 0 []) (initR lay A B hnGenData.nregs) = true := by
  quickRfl

theorem gen271104T_prog : progOK hnGenData.nregs hnGenData.prog = true := by decide +kernel

theorem gen271104T_len :
    (decide (hnGenData.prog.length ≤ 17 * 100) && decide (hnGenData.facts.length ≤ 80 * 8)) =
      true := by
  decide +kernel

#kc_each tCh 0 17
#kc_each tFa 0 80

#kc_forall_tree gen271104T_ch (fun i => tCh i = true) 17 CertificateChecks.KernelFusLay.HN.tCh
#kc_forall_tree gen271104T_fa (fun i => tFa i = true) 80 CertificateChecks.KernelFusLay.HN.tFa

theorem gen271104T_seeds : seedRegsL lay (T.SL.getD 17 []) A B 0 1 = true := by quickRfl

theorem gen271104T_D :
    (genWf 3 hnGenData && hnMod.wf 3 && pcWf (hnTops ++ hnMod.basisPc 3)) = true := by
  decide +kernel

end CertificateChecks.KernelFusLay.HN

end
