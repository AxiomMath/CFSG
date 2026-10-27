module

public import Certificates.Data.GMS78RuCzRigidCheck
public import Certificates.Kernel.GMS78.CzJData
public import Certificates.Kernel.GMS78.CzJPT
public import Certificates.Kernel.GMS78.CzJRW
public import Certificates.Kernel.LocalComp.BlockGen

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.CzJ

open CFSG.KC.GMS CFSG.KLie.CT CFSG.ComponentClassification.GMS78.RuCz

@[expose] noncomputable def GIL : List Nat := (List.range 6).map fun k => fget (LK k) 0 11

@[expose] noncomputable def srchF (j : Nat) : Bool :=
  kSearch RW PAR LAB INV GIL czRels1 czRels3 czRels5 KQ KW FIX D3 D5 CT SOLS j

#lc_blocks srchB srchF 512 1

end CertificateChecks.KernelGMS78.CzJ

end
