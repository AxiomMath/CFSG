module

public import Certificates.Kernel.Misc.RuInv.Data
public import Certificates.Kernel.Misc.RuSq.Chain
public import Certificates.Data.Kernel.Misc.RuInv
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMisc.RuInv

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuInv

@[expose] noncomputable def G : Nat → Nat := gen2 AD.n2 AD.n3

@[expose] noncomputable def GI : Nat → Nat := gen2 AD.n4 AD.n5

@[expose] noncomputable def conjB (q : Nat) : Bool :=
  allN 16 (fun d => conjE E G GI NX.n0 (Nat.add (Nat.mul 16 q) d))

@[expose] noncomputable def hashB (q : Nat) : Bool :=
  allN 16 (fun d => hashE E HS (Nat.add (Nat.mul 16 q) d))

@[expose] noncomputable def covB (q : Nat) : Bool :=
  allN 32 (fun d => covA RuSqS.LR RuSqS.TR E VH (Nat.add (Nat.mul 32 q) d))

end CertificateChecks.KernelMisc.RuInv

end
