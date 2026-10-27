module

public import Certificates.Data.Kernel.OpsLayFill
public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Kernel.LocalComp.LaySnapsChunksF
public import Certificates.Kernel.FusLay.Fi24Seeds
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi24Inputs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelFusLay.Fi24P3 "Certificates/Kernel/FusLay/data/fi24p3.json.gz" 464 11069588544767854970
  (cs : List CFSG.KC.OpsLayK.RChunk)

#lay_snaps_chunks_f CertificateChecks.KernelFusLay.Fi24P3 3 781 CertificateChecks.KernelFusLay.Fi24.A
  CertificateChecks.KernelFusLay.Fi24.B CertificateChecks.KernelFusLay.Fi24P3.cs

namespace CertificateChecks.KernelFusLay.Fi24P3

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus CertificateChecks.KernelFusLay.Fi24

@[expose] def outs : List Nat := [0, 1, 32, 36]

@[expose] noncomputable def chk (k : Nat) : Bool :=
  chunkV lay (cs.getD k (0, [], [])) (SL.getD k []) (SL.getD (k + 1) [])

@[expose] noncomputable def F : List Nat := fillR lay betaFi24P3N outs (SL.getD 6 [])

@[expose] noncomputable def fa (j : Nat) : Bool :=
  factL lay F betaFi24P3N (betaFi24P3.facts.getD j default)

#kc_each chk 0 6
#kc_each fa 0 14

theorem len : cs.length = 6 := by decide +kernel

theorem ren : renOK outs betaFi24P3Prog cs = true := by decide +kernel

#kc_forall_tree ch_all' (fun i => chk i = true) 6 CertificateChecks.KernelFusLay.Fi24P3.chk
#kc_forall_tree fa_all' (fun j => fa j = true) 14 CertificateChecks.KernelFusLay.Fi24P3.fa

theorem ch_all : ∀ i < cs.length, chk i = true := fun i hi => ch_all' i (Nat.lt_of_lt_of_eq hi len)

theorem fa_all : ∀ j < betaFi24P3.facts.length, fa j = true := by
  intro j hj
  have hl : betaFi24P3.facts.length = 14 := by decide +kernel
  exact fa_all' j (Nat.lt_of_lt_of_eq hj hl)

theorem fin_in : (betaFi24P3.facts.all (factIn outs) && memB betaFi24P3.rA outs &&
    memB betaFi24P3.rB outs) = true := by decide +kernel

theorem seeds : seedRegsL lay F A B betaFi24P3.rA betaFi24P3.rB = true := by quickRfl

theorem ren_neg : (!renOK [0, 1, 36, 32] betaFi24P3Prog cs) = true := by decide +kernel

theorem ch_neg : (!chunkV lay (cs.getD 1 (0, [], [])) (SL.getD 2 []) (SL.getD 2 [])) = true := by
  quickRfl

theorem fa_neg : (!factL lay (initR lay A B betaFi24P3N) betaFi24P3N
    (betaFi24P3.facts.getD 5 default)) = true := by quickRfl

theorem seeds_neg : (!seedRegsL lay F B A betaFi24P3.rA betaFi24P3.rB) = true := by quickRfl

end CertificateChecks.KernelFusLay.Fi24P3

end
