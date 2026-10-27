module

public import Certificates.Kernel.Sporadic.ON8.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanParCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPar

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.ONSchreier
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
open CertificateChecks.KernelSpor.ON (TT UU)
open CertificateChecks.KernelSpor.ON3 (ZT QT DT siftT siftM blkK)
open CertificateChecks.KernelSpor.ON8 (onP)

@[expose] noncomputable def wK (w : List Int) (x : Nat) : Nat := w.foldr (GZ TT UU) x

@[expose] noncomputable def vK (x : Nat) : Nat := wK onpVWord x
@[expose] noncomputable def xK (x : Nat) : Nat := wK onpXWord x
@[expose] noncomputable def mK (x : Nat) : Nat := wK onpMWord x
@[expose] noncomputable def nK (x : Nat) : Nat := wK onpNWord x
@[expose] noncomputable def gK (x : Nat) : Nat := nK (xK (mK (xK x)))

@[expose] noncomputable def vSift : Bool := siftT vK
@[expose] noncomputable def mSift : Bool := siftM mK
@[expose] noncomputable def nSift : Bool := siftM nK

@[expose] noncomputable def rel1 : Bool := onP (fun y => xK (ZT y)) (fun y => vK (ZT (xK y)))
@[expose] noncomputable def rel2 : Bool := onP (fun y => xK (vK y)) (fun y => ZT (xK y))
@[expose] noncomputable def rel3 : Bool := onP (fun y => xK (xK (xK y))) (fun y => y)
@[expose] noncomputable def rel4 : Bool := onP (fun y => gK (ZT y)) (fun y => DT 0 (gK y))
@[expose] noncomputable def rel5 : Bool := onP (fun y => QT (QT y)) ZT

@[expose] noncomputable def rOK : Bool :=
  allN 32 fun k => bAnd(Nat.blt onpV32[k]! 32,
    Nat.beq Data.TPoints[onpV32[k]!]! (vK Data.TPoints[k]!))

@[expose] noncomputable def bOK : Bool := blkK vK fun i => onpVB[i]!

end CertificateChecks.KernelSpor.ONPar

end
