module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySnaps
public import Certificates.Kernel.TcGen.Fi23
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi23Inputs
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi23Inputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

#lay_snaps CertificateChecks.KernelFusLay.Fi23P3.S 3 253 CertificateChecks.KernelTc.Fi23.A
  CertificateChecks.KernelTc.Fi23.B CFSG.RankThree.PartOne.CTP.Fus.betaFi23P3Prog 1106 200

public section

namespace CertificateChecks.KernelFusLay.Fi23P3

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus CertificateChecks.KernelTc.Fi23

@[expose] noncomputable def ch (i : Nat) : Bool :=
  chunkL lay betaFi23P3Prog 200 i (S.SL.getD i []) (S.SL.getD (i + 1) [])

@[expose] noncomputable def fa (i : Nat) : Bool :=
  factsL lay (S.SL.getD 6 []) betaFi23P3N betaFi23P3.facts 1 i

theorem init : eqL (S.SL.getD 0 []) (initR lay A B betaFi23P3N) = true := by quickRfl

#kc_each ch 0 6
#kc_each fa 0 68

#kc_forall_tree ch_all (fun i => ch i = true) 6 CertificateChecks.KernelFusLay.Fi23P3.ch
#kc_forall_tree fa_all (fun i => fa i = true) 68 CertificateChecks.KernelFusLay.Fi23P3.fa

theorem seeds : seedRegsL lay (S.SL.getD 6 []) A B betaFi23P3.rA betaFi23P3.rB = true := by
  quickRfl

theorem ch_neg : (!chunkL lay betaFi23P3Prog 200 0 (S.SL.getD 0 []) (S.SL.getD 2 [])) = true := by
  quickRfl

theorem fa_neg : (!factsL lay (S.SL.getD 0 []) betaFi23P3N betaFi23P3.facts 1 5) = true := by
  quickRfl

theorem seeds_neg : (!seedRegsL lay (S.SL.getD 6 []) B A betaFi23P3.rA betaFi23P3.rB) = true := by
  quickRfl

end CertificateChecks.KernelFusLay.Fi23P3

end
