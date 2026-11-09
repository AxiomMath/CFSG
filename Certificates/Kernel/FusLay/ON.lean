module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayFill
public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Kernel.LocalComp.LaySnapsChunksF
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusONInputs
import all CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelFusLay.ON 3 154
  CFSG.Blueprint.NativeSporadic.ONSeed1 CFSG.Blueprint.NativeSporadic.ONSeed2

public section

#kc_repo #kc_json CertificateChecks.KernelFusLay.ON "Certificates/Kernel/FusLay/data/onp3.json" 7551 9159404700667956941
  (cs : List CFSG.KC.OpsLayK.RChunk)

#lay_snaps_chunks_f CertificateChecks.KernelFusLay.ON 3 154 CertificateChecks.KernelFusLay.ON.A
  CertificateChecks.KernelFusLay.ON.B CertificateChecks.KernelFusLay.ON.cs

namespace CertificateChecks.KernelFusLay.ON

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus

@[expose] def outs : List Nat := [0, 1, 671, 617]

@[expose] noncomputable def chk (k : Nat) : Bool :=
  chunkV lay (cs.getD k (0, [], [])) (SL.getD k []) (SL.getD (k + 1) [])

@[expose] noncomputable def F : List Nat := fillR lay betaONP3N outs (SL.getD 14 [])

@[expose] noncomputable def fa (j : Nat) : Bool :=
  factL lay F betaONP3N (betaONP3.facts.getD j default)

#kc_each chk 0 14
#kc_each fa 0 14

theorem len : cs.length = 14 := by decide +kernel

theorem ren : renOK outs betaONP3Prog cs = true := by quickRfl

#kc_forall_tree ch_all' (fun i => chk i = true) 14 CertificateChecks.KernelFusLay.ON.chk
#kc_forall_tree fa_all' (fun j => fa j = true) 14 CertificateChecks.KernelFusLay.ON.fa

theorem ch_all : ∀ i < cs.length, chk i = true := fun i hi => ch_all' i (Nat.lt_of_lt_of_eq hi len)

theorem fa_all : ∀ j < betaONP3.facts.length, fa j = true := by
  intro j hj
  have hl : betaONP3.facts.length = 14 := by decide +kernel
  exact fa_all' j (Nat.lt_of_lt_of_eq hj hl)

theorem fin_in : (betaONP3.facts.all (factIn outs) && memB betaONP3.rA outs &&
    memB betaONP3.rB outs) = true := by decide +kernel

theorem seeds : seedRegsL lay F A B betaONP3.rA betaONP3.rB = true := by quickRfl

end CertificateChecks.KernelFusLay.ON

end
