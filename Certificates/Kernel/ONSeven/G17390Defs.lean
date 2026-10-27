module

public import Certificates.Kernel.ONSeven.Defs
public import Certificates.Kernel.Sporadic.ON3.Words
public import CFSG.RankThree.Native.ONSevenData

public section

namespace CertificateChecks.KernelSpor.ONS

open CFSG.KS.TW CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON (TT)
open CertificateChecks.KernelSpor.ON3 (invW)

@[expose] def gW17390 (i : Nat) : List Int := (onSevenCentWords[i / 4]!)[i % 4]!

@[expose] noncomputable def WN17390 (u : List Int) (x : Nat) : Nat :=
  u.foldr (GZ (fun i => WW (gW17390 i)) (fun i => WW (invW (gW17390 i)))) x

@[expose] noncomputable def ch17390 (u v : List Int) (x : Nat) : Bool :=
  Nat.beq (WN17390 u x) (TT 0 x) && Nat.beq (WN17390 v x) (TT 1 x)

end CertificateChecks.KernelSpor.ONS

end
