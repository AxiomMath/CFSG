module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySnaps
public import Certificates.Kernel.TcGen.Fi23
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Fi23Inputs
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Fi23Inputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

#lay_snaps CertificateChecks.KernelFusLay.Fi23P5.S 3 253 CertificateChecks.KernelTc.Fi23.A
  CertificateChecks.KernelTc.Fi23.B CFSG.RankThree.PartOne.CTP.Fus.fusD2Fi23Prog 165 60

public section

namespace CertificateChecks.KernelFusLay.Fi23P5

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus CertificateChecks.KernelTc.Fi23

@[expose] noncomputable def ch (i : Nat) : Bool :=
  chunkL lay fusD2Fi23Prog 60 i (S.SL.getD i []) (S.SL.getD (i + 1) [])

@[expose] noncomputable def fa (i : Nat) : Bool :=
  factsL lay (S.SL.getD 3 []) fusD2Fi23N fusD2Fi23.facts 2 i

theorem init : eqL (S.SL.getD 0 []) (initR lay A B fusD2Fi23N) = true := by quickRfl

#kc_each ch 0 3
#kc_each fa 0 19

#kc_forall_tree ch_all (fun i => ch i = true) 3 CertificateChecks.KernelFusLay.Fi23P5.ch
#kc_forall_tree fa_all (fun i => fa i = true) 19 CertificateChecks.KernelFusLay.Fi23P5.fa

theorem seeds : seedRegsL lay (S.SL.getD 3 []) A B fusD2Fi23.rA fusD2Fi23.rB = true := by
  quickRfl

theorem ch_neg : (!chunkL lay fusD2Fi23Prog 60 0 (S.SL.getD 0 []) (S.SL.getD 2 [])) = true := by
  quickRfl

theorem fa_neg : (!factsL lay (S.SL.getD 0 []) fusD2Fi23N fusD2Fi23.facts 2 2) = true := by
  quickRfl

theorem seeds_neg : (!seedRegsL lay (S.SL.getD 3 []) B A fusD2Fi23.rA fusD2Fi23.rB) = true := by
  quickRfl

end CertificateChecks.KernelFusLay.Fi23P5

end
