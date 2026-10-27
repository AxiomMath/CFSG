module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Kernel.LocalComp.LaySnaps
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi23ThreeData
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi23ThreeData
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000
set_option Elab.async false

#lay_seeds CertificateChecks.KernelTc.Fi23 3 253
  CFSG.Blueprint.NativeSporadic.Fi23Seed1 CFSG.Blueprint.NativeSporadic.Fi23Seed2

#lay_snaps CertificateChecks.KernelTc.Fi23.T 3 253 CertificateChecks.KernelTc.Fi23.A
  CertificateChecks.KernelTc.Fi23.B CFSG.AGLEmbedding.R3.Fi23Three.tcProg 87 200
#lay_snaps CertificateChecks.KernelTc.Fi23.C 3 253 CertificateChecks.KernelTc.Fi23.A
  CertificateChecks.KernelTc.Fi23.B CFSG.AGLEmbedding.R3.Fi23Three.cpProg 71 200

public section

namespace CertificateChecks.KernelTc.Fi23

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi23Three

@[expose] noncomputable def tcCh (i : Nat) : Bool :=
  chunkL lay tcProg 200 i (T.SL.getD i []) (T.SL.getD (i + 1) [])

@[expose] noncomputable def tcFa (i : Nat) : Bool :=
  factsL lay (T.SL.getD 6 []) tcNregs tcSpec.facts 25 i

@[expose] noncomputable def cpCh (i : Nat) : Bool :=
  chunkL lay cpProg 200 i (C.SL.getD i []) (C.SL.getD (i + 1) [])

@[expose] noncomputable def cpFa (i : Nat) : Bool :=
  factsL lay (C.SL.getD 5 []) cpNregs cpSpec.facts 25 i

theorem tcInit : eqL (T.SL.getD 0 []) (initR lay A B tcNregs) = true := by quickRfl

theorem cpInit : eqL (C.SL.getD 0 []) (initR lay A B cpNregs) = true := by quickRfl

#kc_each tcCh 0 6
#kc_each tcFa 0 10
#kc_each cpCh 0 5
#kc_each cpFa 0 6

theorem tcSeeds : seedRegsL lay (T.SL.getD 6 []) A B tcSpec.rA tcSpec.rB = true := by quickRfl

theorem cpSeeds : seedRegsL lay (C.SL.getD 5 []) A B cpSpec.rA cpSpec.rB = true := by quickRfl

theorem ch_neg : (!chunkL lay tcProg 200 0 (T.SL.getD 0 []) (C.SL.getD 1 [])) = true := by
  quickRfl

theorem seeds_neg : (!seedRegsL lay (T.SL.getD 6 []) B A tcSpec.rA tcSpec.rB) = true := by
  quickRfl

end CertificateChecks.KernelTc.Fi23

end
