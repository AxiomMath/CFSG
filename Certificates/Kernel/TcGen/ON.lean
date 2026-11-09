module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Data.Kernel.OpsLayTab
public import Certificates.Data.Kernel.OpsLayFill
public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Kernel.LocalComp.LaySnaps
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONThreeData
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONThreeData
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000
set_option Elab.async false

#lay_seeds CertificateChecks.KernelTc.ON 3 154
  CFSG.Blueprint.NativeSporadic.ONSeed1 CFSG.Blueprint.NativeSporadic.ONSeed2

#lay_snaps CertificateChecks.KernelTc.ON.T 3 154 CertificateChecks.KernelTc.ON.A
  CertificateChecks.KernelTc.ON.B CFSG.AGLEmbedding.R3.ONThree.tcProg 33 100
#lay_snaps CertificateChecks.KernelTc.ON.C 3 154 CertificateChecks.KernelTc.ON.A
  CertificateChecks.KernelTc.ON.B CFSG.AGLEmbedding.R3.ONThree.cpProg 26 100

public section

namespace CertificateChecks.KernelTc.ON

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.ONThree

@[expose] noncomputable def tabC (i : Nat) : Bool :=
  CFSG.KC.OpsLayTab.tabF lay.mul (powK lay) C.VT C.KT C.N (3 + i * 64) 64

#kc_each tabC 0 35

@[expose] noncomputable def symP (prog : List CFSG.SectionRank.Native.Op) (VS : List Nat)
    (I0 IF : Nat) (S : List Nat) (n : Nat) : Bool :=
  CFSG.KC.OpsLayTab.symT C.KT C.N n prog VS I0 IF &&
    eqL (CFSG.KC.OpsLayTab.regsT C.VT n I0) (initR lay A B n) &&
    eqL (CFSG.KC.OpsLayTab.regsT C.VT n IF) S

theorem tcSym : symP tcProg T.VS T.I0 T.IF (T.SL.getD 11 []) tcNregs = true := by quickRfl

theorem cpSym : symP cpProg C.VS C.I0 C.IF (C.SL.getD 11 []) cpNregs = true := by quickRfl

@[expose] def tcFs : List CFSG.RankThree.Asc83Table.Native.MFact :=
  { tcSpec with der := [] }.facts ++ tcSpec.der.map fun d => .ord d.reg d.ord

@[expose] def cpFs : List CFSG.RankThree.Asc83Table.Native.MFact :=
  { cpSpec with der := [] }.facts ++ cpSpec.der.map fun d => .ord d.reg d.ord

@[expose] noncomputable def tcFa (i : Nat) : Bool :=
  ((tcFs.drop (i * 12)).take 12).all (factL1 lay (T.SL.getD 11 []) tcNregs)

@[expose] noncomputable def cpFa (i : Nat) : Bool :=
  ((cpFs.drop (i * 12)).take 12).all (factL1 lay (C.SL.getD 11 []) cpNregs)

#kc_each tcFa 0 11
#kc_each cpFa 0 7

theorem tcSeeds : seedRegsL lay (T.SL.getD 11 []) A B tcSpec.rA tcSpec.rB = true := by quickRfl

theorem cpSeeds : seedRegsL lay (C.SL.getD 11 []) A B cpSpec.rA cpSpec.rB = true := by quickRfl

theorem ch_neg : (!CFSG.KC.OpsLayTab.symT C.KT C.N cpNregs (cpProg.take 20) (C.VS.drop 1) C.I0
    C.I0) = true := by
  quickRfl

theorem tab_neg : (!CFSG.KC.OpsLayTab.entF lay.mul (powK lay) C.VT (0, 2, 2) 0) = true := by
  quickRfl

theorem eq_neg : (!seedsL lay A B ⟨2, [], [.eq [(0, 1)] [(1, 1)]]⟩ 0 1) = true := by
  quickRfl

end CertificateChecks.KernelTc.ON

end
