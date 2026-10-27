module

public import Certificates.Kernel.Misc.KGroups.U33Data
public import Certificates.Kernel.Misc.KGroups.U33Tabs
public import Certificates.Data.Kernel.Misc.PermM22
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CertificateChecks.KernelMisc.U33K

open CFSG.KC.Ord CFSG.KC.Misc.M22 CFSG.KC.LQT.P

@[expose] noncomputable def AG (a : Nat) : Nat := nthL genA a
@[expose] noncomputable def UG (a : Nat) : Nat := nthL genUV a
@[expose] noncomputable def RG (a : Nat) : Nat := nthL repL a
@[expose] noncomputable def WAB (j : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) wordsAB j

@[expose] noncomputable def inP (c : Nat) : Bool := anyN 6048 fun j => Nat.beq (EP j) c

@[expose] noncomputable def inA (c : Nat) : Bool := anyN 12096 fun j => Nat.beq (EA j) c

end CertificateChecks.KernelMisc.U33K

end
