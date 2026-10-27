module

public import Certificates.Kernel.Sporadic.ON.Neg
public import Certificates.Kernel.Sporadic.ONLine.GenTabs
public import Certificates.Data.Kernel.Spor.ONLineK
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONLine

open CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native

meta def lineM : VOrbit := lineBFS colsA colsB (digitsW CFSG.ONSchreier.Data.rootDigits) 122760

meta def noS : Array (Array Nat) := #[]

meta def noW : Array (List Int) := #[]

meta def tabsM : Array (Array Nat) :=
  let U := lineM
  let pi := piTab CertificateChecks.KernelSpor.ON.orbM (posOf (indexOf U.keys) 122760)
  let lp := U.keys.map fun x =>
    ((List.range 154).find? fun j => x.toV.p.testBit j || x.toV.m.testBit j).getD 0
  #[pi, piPre 122760 pi, lp]

end CertificateChecks.KernelSpor.ONLine

#kon_data CertificateChecks.KernelSpor.ONL CertificateChecks.KernelSpor.ONLine.lineM
  CertificateChecks.KernelSpor.ONLine.noS CertificateChecks.KernelSpor.ON.colsAM
  CertificateChecks.KernelSpor.ON.colsBM CertificateChecks.KernelSpor.ONLine.noW 120

#kon_tables CertificateChecks.KernelSpor.ONLine.tabsM CertificateChecks.KernelSpor.ONL.PI
  CertificateChecks.KernelSpor.ONL.PRE CertificateChecks.KernelSpor.ONL.LP

namespace CertificateChecks.KernelSpor.ONLine

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def lnS (s : Nat) : Bool :=
  lineRange ONL.K ONL.LP ONV.LA ONV.LB ONL.A ONL.B (nat_lit 122760) (Nat.mul s (nat_lit 120))
    (nat_lit 120)

@[expose] noncomputable def lordS (s : Nat) : Bool :=
  Nat.beq (ordRun ONL.A ONL.B (Nat.mul s (nat_lit 120)) (nat_lit 120) (ONL.NX s))
    (ONL.NX (Nat.succ s))

@[expose] noncomputable def lsortS (s : Nat) : Bool :=
  sortRange ONL.K ONL.SO ONL.SOI (nat_lit 122760) (Nat.mul s (nat_lit 120)) (nat_lit 120)

@[expose] noncomputable def piS (s : Nat) : Bool :=
  piRange ONV.K ONN.NEG ONV.A ONV.B ONL.K ONL.A ONL.B ONL.PI (nat_lit 122760)
    (Nat.mul s (nat_lit 240)) (nat_lit 240)

@[expose] noncomputable def preS (s : Nat) : Bool :=
  preRange ONL.PI ONL.PRE (nat_lit 245520) (Nat.mul s (nat_lit 120)) (nat_lit 120)

end CertificateChecks.KernelSpor.ONLine

end
