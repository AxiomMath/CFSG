module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySnaps
public import Certificates.Kernel.TcGen.ON
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData4
meta import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData2
meta import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData4
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

meta def CertificateChecks.KernelMP.ON.pProg : List CFSG.SectionRank.Native.Op :=
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal.on_31_claims.prog

meta def CertificateChecks.KernelMP.ON.gProg : List CFSG.SectionRank.Native.Op :=
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal.on_5_claims.prog

#lay_snaps CertificateChecks.KernelMP.ON.P 3 154 CertificateChecks.KernelTc.ON.A
  CertificateChecks.KernelTc.ON.B CertificateChecks.KernelMP.ON.pProg 11 24
#lay_snaps CertificateChecks.KernelMP.ON.G 3 154 CertificateChecks.KernelTc.ON.A
  CertificateChecks.KernelTc.ON.B CertificateChecks.KernelMP.ON.gProg 14 100

public section

namespace CertificateChecks.KernelMP.ON

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CertificateChecks.KernelTc.ON

@[expose] noncomputable def pCh (i : Nat) : Bool :=
  chunkL lay on_31_claims.prog 24 i (P.SL.getD i []) (P.SL.getD (i + 1) [])

@[expose] noncomputable def pFa (i : Nat) : Bool :=
  factsL lay (P.SL.getD 4 []) on_31_claims.nregs on_31_claims.facts 1 i

@[expose] noncomputable def gCh (i : Nat) : Bool :=
  chunkL lay on_5_claims.prog 100 i (G.SL.getD i []) (G.SL.getD (i + 1) [])

@[expose] noncomputable def gFa (i : Nat) : Bool :=
  factsL lay (G.SL.getD 28 []) on_5_claims.nregs on_5_claims.facts 1 i

theorem pInit : eqL (P.SL.getD 0 []) (initR lay A B on_31_claims.nregs) = true := by quickRfl

theorem gInit : eqL (G.SL.getD 0 []) (initR lay A B on_5_claims.nregs) = true := by quickRfl

#kc_each pCh 0 4
#kc_each pFa 0 4
#kc_each gCh 0 28
#kc_each gFa 0 25

#kc_forall_tree pCh_all (fun i => pCh i = true) 4 CertificateChecks.KernelMP.ON.pCh
#kc_forall_tree pFa_all (fun i => pFa i = true) 4 CertificateChecks.KernelMP.ON.pFa
#kc_forall_tree gCh_all (fun i => gCh i = true) 28 CertificateChecks.KernelMP.ON.gCh
#kc_forall_tree gFa_all (fun i => gFa i = true) 25 CertificateChecks.KernelMP.ON.gFa

theorem pSeeds : seedRegsL lay (P.SL.getD 4 []) A B 0 1 = true := by quickRfl

theorem gSeeds : seedRegsL lay (G.SL.getD 28 []) A B 0 1 = true := by quickRfl

theorem g_wf : on_5_claims.wf = true := by decide +kernel

theorem ch_neg : (!chunkL lay on_5_claims.prog 100 0 (G.SL.getD 0 []) (G.SL.getD 2 [])) = true := by
  quickRfl

theorem fa_neg : (!factsL lay (P.SL.getD 0 []) on_31_claims.nregs on_31_claims.facts 1 2) = true := by
  quickRfl

theorem seeds_neg : (!seedRegsL lay (G.SL.getD 28 []) B A 0 1) = true := by
  quickRfl

end CertificateChecks.KernelMP.ON

end
