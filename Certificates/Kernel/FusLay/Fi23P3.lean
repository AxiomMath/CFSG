module

public import Certificates.Data.Kernel.OpsLayFill
public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Kernel.LocalComp.LaySnapsChunksF
public import Certificates.Kernel.TcGen.Fi23
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi23Inputs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

#kc_repo #kc_json CertificateChecks.KernelFusLay.Fi23P3 "Certificates/Kernel/FusLay/data/fi23p3.json" 14744 16487016191279340522
  (cs : List CFSG.KC.OpsLayK.RChunk)

#lay_snaps_chunks_f CertificateChecks.KernelFusLay.Fi23P3 3 253 CertificateChecks.KernelTc.Fi23.A
  CertificateChecks.KernelTc.Fi23.B CertificateChecks.KernelFusLay.Fi23P3.cs

namespace CertificateChecks.KernelFusLay.Fi23P3

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus CertificateChecks.KernelTc.Fi23

@[expose] def outs : List Nat :=
  [0, 1, 94, 95, 23, 171, 249, 303, 348, 420, 483, 530, 583, 632, 675, 722, 776, 832, 896, 964,
    1000, 1019, 1043, 1105]

@[expose] noncomputable def chk (k : Nat) : Bool :=
  chunkV lay (cs.getD k (0, [], [])) (SL.getD k []) (SL.getD (k + 1) [])

@[expose] noncomputable def F : List Nat := fillR lay betaFi23P3N outs (SL.getD 23 [])

@[expose] noncomputable def fa (j : Nat) : Bool :=
  factL lay F betaFi23P3N (betaFi23P3.facts.getD j default)

#kc_each chk 0 23
#kc_each fa 0 68

theorem len : cs.length = 23 := by decide +kernel

theorem ren : renOK outs betaFi23P3Prog cs = true := by quickRfl

#kc_forall_tree ch_all' (fun i => chk i = true) 23 CertificateChecks.KernelFusLay.Fi23P3.chk
#kc_forall_tree fa_all' (fun j => fa j = true) 68 CertificateChecks.KernelFusLay.Fi23P3.fa

theorem ch_all : ∀ i < cs.length, chk i = true := fun i hi => ch_all' i (Nat.lt_of_lt_of_eq hi len)

theorem fa_all : ∀ j < betaFi23P3.facts.length, fa j = true := by
  intro j hj
  have hl : betaFi23P3.facts.length = 68 := by decide +kernel
  exact fa_all' j (Nat.lt_of_lt_of_eq hj hl)

theorem fin_in : (betaFi23P3.facts.all (factIn outs) && memB betaFi23P3.rA outs &&
    memB betaFi23P3.rB outs) = true := by decide +kernel

theorem seeds : seedRegsL lay F A B betaFi23P3.rA betaFi23P3.rB = true := by quickRfl

theorem ren_neg : (!renOK outs betaFi23P3Prog.tail cs) = true := by quickRfl

@[expose] noncomputable def ng (k : Nat) : Bool :=
  [!chunkV lay (cs.getD 1 (0, [], [])) (SL.getD 1 []) (SL.getD 1 []),
    !factL lay (initR lay A B betaFi23P3N) betaFi23P3N (betaFi23P3.facts.getD 5 default),
    !seedRegsL lay F B A betaFi23P3.rA betaFi23P3.rB].getD k false

#kc_each ng 0 3

end CertificateChecks.KernelFusLay.Fi23P3

end
