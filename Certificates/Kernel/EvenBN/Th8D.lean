module

public import Certificates.Kernel.LocalComp.M1Gen
public import Certificates.Kernel.LocalComp.ThSeeds
meta import Certificates.Kernel.LocalComp.ThSeeds

#lc_m1mat CertificateChecks.Th8.A CertificateChecks.KernelLC.thSeedA 248
#lc_m1mat CertificateChecks.Th8.B CertificateChecks.KernelLC.thSeedB 248

public section

namespace CertificateChecks.Th8

open CFSG.KC.M1F2

@[expose] noncomputable def mm (X Y : Nat) : Nat := mulF 248 X Y

@[expose] noncomputable def r10 (a b : Nat) : Nat :=
  mm (mm (mm (mm (mm (mm (mm a b) (mm a b)) (mm a b)) (mm a (mm b b))) (mm a b)) (mm a (mm b b)))
    (mm a (mm b b))

@[expose] noncomputable def r11 (a b : Nat) : Nat := mm (r10 a b) (mm (r10 a b) (r10 a b))

@[expose] noncomputable def x4 (a b : Nat) : Nat :=
  mm (mm (r11 a b) (r11 a b)) (mm (r11 a b) (r11 a b))

@[expose] noncomputable def x8 (a b : Nat) : Nat := mm (x4 a b) (x4 a b)

@[expose] noncomputable def moves0 (X : Nat) : Bool :=
  (List.range 248).any fun j => (vmF 248 X (1 <<< 0)).testBit j != (1 <<< 0 : Nat).testBit j

end CertificateChecks.Th8

end
