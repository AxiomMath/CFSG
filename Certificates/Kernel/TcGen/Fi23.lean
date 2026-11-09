module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Data.Kernel.OpsLayTab
public import Certificates.Data.Kernel.OpsLayFill
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

@[expose] noncomputable def tabC (i : Nat) : Bool :=
  CFSG.KC.OpsLayTab.tabF lay.mul (powK lay) C.VT C.KT C.N (3 + i * 16) 16

#kc_each tabC 0 140

@[expose] noncomputable def symP (prog : List CFSG.SectionRank.Native.Op) (VS : List Nat)
    (I0 IF : Nat) (S : List Nat) (n : Nat) : Bool :=
  CFSG.KC.OpsLayTab.symT C.KT C.N n prog VS I0 IF &&
    eqL (CFSG.KC.OpsLayTab.regsT C.VT n I0) (initR lay A B n) &&
    eqL (CFSG.KC.OpsLayTab.regsT C.VT n IF) S

theorem tcSym : symP tcProg T.VS T.I0 T.IF (T.SL.getD 6 []) tcNregs = true := by quickRfl

theorem cpSym : symP cpProg C.VS C.I0 C.IF (C.SL.getD 5 []) cpNregs = true := by quickRfl

@[expose] def tcFs : List CFSG.RankThree.Asc83Table.Native.MFact :=
  { tcSpec with der := [] }.facts ++ tcSpec.der.map fun d => .ord d.reg d.ord

@[expose] def cpFs : List CFSG.RankThree.Asc83Table.Native.MFact :=
  { cpSpec with der := [] }.facts ++ cpSpec.der.map fun d => .ord d.reg d.ord

@[expose] noncomputable def tcFa (i : Nat) : Bool :=
  ((tcFs.drop (i * 5)).take 5).all (factL1 lay (T.SL.getD 6 []) tcNregs)

@[expose] noncomputable def cpFa (i : Nat) : Bool :=
  ((cpFs.drop (i * 5)).take 5).all (factL1 lay (C.SL.getD 5 []) cpNregs)

#kc_each tcFa 0 50
#kc_each cpFa 0 30

theorem tcSeeds : seedRegsL lay (T.SL.getD 6 []) A B tcSpec.rA tcSpec.rB = true := by quickRfl

theorem cpSeeds : seedRegsL lay (C.SL.getD 5 []) A B cpSpec.rA cpSpec.rB = true := by quickRfl

theorem ch_neg : (!CFSG.KC.OpsLayTab.symT C.KT C.N cpNregs (cpProg.take 20) (C.VS.drop 1) C.I0
    C.I0) = true := by
  quickRfl

theorem tab_neg : (!CFSG.KC.OpsLayTab.entF lay.mul (powK lay) C.VT (0, 2, 2) 0) = true := by
  quickRfl

theorem seeds_neg : (!seedRegsL lay (T.SL.getD 6 []) B A tcSpec.rA tcSpec.rB) = true := by
  quickRfl

end CertificateChecks.KernelTc.Fi23

end
