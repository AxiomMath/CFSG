module

public import Certificates.Data.Kernel.OpsLayFill
public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Kernel.LocalComp.LaySnapsChunksF
public import Certificates.Kernel.FusLay.Fi24Seeds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Fi24primeInputs
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Fi24primeInputs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelFusLay.Fi24P5 "Certificates/Kernel/FusLay/data/fi24p5.json.gz" 2643 2324860897212928783
  (cs : List CFSG.KC.OpsLayK.RChunk)

#lay_snaps_chunks_f CertificateChecks.KernelFusLay.Fi24P5 3 781 CertificateChecks.KernelFusLay.Fi24.A
  CertificateChecks.KernelFusLay.Fi24.B CertificateChecks.KernelFusLay.Fi24P5.cs

namespace CertificateChecks.KernelFusLay.Fi24P5

@[expose] def outs : List Nat := [0, 1, 49, 59, 72, 87, 100, 101, 109, 114, 158]

meta def wB : List (Nat × Nat) := CFSG.RankThree.PartOne.CTP.Fus.fusD2Fi24.wB

end CertificateChecks.KernelFusLay.Fi24P5

#lay_wsegs_f CertificateChecks.KernelFusLay.Fi24P5.W 3 781 CertificateChecks.KernelFusLay.Fi24P5.S20
  CertificateChecks.KernelFusLay.Fi24P5.outs CertificateChecks.KernelFusLay.Fi24P5.wB 8

namespace CertificateChecks.KernelFusLay.Fi24P5

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus CertificateChecks.KernelFusLay.Fi24

@[expose] noncomputable def ch (k : Nat) : Bool :=
  chunkV lay (cs.getD k (0, [], [])) (SL.getD k []) (SL.getD (k + 1) [])

@[expose] noncomputable def ch9586 (k : Nat) : Bool := ch k

@[expose] noncomputable def F : List Nat := fillR lay fusD2Fi24N outs (SL.getD 20 [])

@[expose] noncomputable def fa (j : Nat) : Bool :=
  factL lay F fusD2Fi24N (fusD2Fi24.facts.getD j default)

@[expose] noncomputable def seg (i : Nat) : Bool :=
  wsegL lay F fusD2Fi24.wB 8 i (W.WL.getD i lay.ONE) (W.WL.getD (i + 1) lay.ONE)

end CertificateChecks.KernelFusLay.Fi24P5

end
