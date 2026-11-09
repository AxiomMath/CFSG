module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayFus
public import Certificates.Data.Kernel.OpsLayFill
public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Kernel.LocalComp.LaySnapsChunksF
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusHNInputs
import all CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelFusLay.HN 5 133
  CFSG.Blueprint.NativeSporadic.HNSeed1 CFSG.Blueprint.NativeSporadic.HNSeed2

public section

namespace CertificateChecks.KernelFusLay.HN

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus

theorem fus9480_K : fusL lay A B betaHNP3N betaHNP3Prog betaHNP3 = true := by decide +kernel

theorem fus9480_neg : (!fusL lay B A betaHNP3N betaHNP3Prog betaHNP3) = true := by
  decide +kernel

end CertificateChecks.KernelFusLay.HN

#kc_repo #kc_json CertificateChecks.KernelFusLay.HN.P5 "Certificates/Kernel/FusLay/data/hnp5.json" 3117 11501277766392336773
  (cs : List CFSG.KC.OpsLayK.RChunk)

#lay_snaps_chunks_f CertificateChecks.KernelFusLay.HN.P5 5 133 CertificateChecks.KernelFusLay.HN.A
  CertificateChecks.KernelFusLay.HN.B CertificateChecks.KernelFusLay.HN.P5.cs

namespace CertificateChecks.KernelFusLay.HN.P5

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus

@[expose] def outs : List Nat := [0, 1, 486, 550]

@[expose] noncomputable def chk (k : Nat) : Bool :=
  chunkV lay (cs.getD k (0, [], [])) (SL.getD k []) (SL.getD (k + 1) [])

@[expose] noncomputable def F : List Nat := fillR lay betaHNP5N outs (SL.getD 9 [])

@[expose] noncomputable def fa (j : Nat) : Bool :=
  factL lay F betaHNP5N (betaHNP5.facts.getD j default)

#kc_each chk 0 9

#kc_each fa 0 14

theorem len : cs.length = 9 := by decide +kernel

theorem ren : renOK outs betaHNP5Prog cs = true := by decide +kernel

#kc_forall_tree ch_all' (fun i => chk i = true) 9 CertificateChecks.KernelFusLay.HN.P5.chk
#kc_forall_tree fa_all' (fun j => fa j = true) 14 CertificateChecks.KernelFusLay.HN.P5.fa

theorem ch_all : ∀ i < cs.length, chk i = true := fun i hi => ch_all' i (Nat.lt_of_lt_of_eq hi len)

theorem fa_all : ∀ j < betaHNP5.facts.length, fa j = true := by
  intro j hj
  have hl : betaHNP5.facts.length = 14 := by decide +kernel
  exact fa_all' j (Nat.lt_of_lt_of_eq hj hl)

theorem fin_in : (betaHNP5.facts.all (factIn outs) && memB betaHNP5.rA outs &&
    memB betaHNP5.rB outs) = true := by decide +kernel

theorem seeds : seedRegsL lay F A B betaHNP5.rA betaHNP5.rB = true := by quickRfl

theorem ren_neg : (!renOK [0, 1, 550, 486] betaHNP5Prog cs) = true := by decide +kernel

@[expose] noncomputable def ng (k : Nat) : Bool :=
  [!chunkV lay (cs.getD 1 (0, [], [])) (SL.getD 1 []) (SL.getD 1 []),
    !factL lay (initR lay A B betaHNP5N) betaHNP5N (betaHNP5.facts.getD 5 default),
    !seedRegsL lay F B A betaHNP5.rA betaHNP5.rB].getD k false

#kc_each ng 0 3

end CertificateChecks.KernelFusLay.HN.P5

end
