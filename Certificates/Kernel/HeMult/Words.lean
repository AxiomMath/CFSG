module

public import CFSG.Sporadic.Recognition.HeMultiplierInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG

public section

namespace CertificateChecks.KernelHeMult

open CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.HeMultiplier

@[expose] noncomputable def rels4 : List (List (Nat × Bool)) := heRels.map encW

@[expose] noncomputable def rels3 : List (List (Nat × Bool)) := heRels3.map encW

@[expose] noncomputable def rels2 : List (List (Nat × Bool)) := heRels2.map encW

@[expose] noncomputable def cover4 : List (List (Nat × Bool)) := heCover.map encW

@[expose] noncomputable def cover3 : List (List (Nat × Bool)) := heCover3.map encW

@[expose] noncomputable def cover2 : List (List (Nat × Bool)) := heCover2.map encW

end CertificateChecks.KernelHeMult

end
