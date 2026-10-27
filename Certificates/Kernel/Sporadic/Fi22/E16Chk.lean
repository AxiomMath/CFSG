module

public import Certificates.Kernel.Sporadic.Fi22.E16T
public import Certificates.Kernel.Sporadic.Fi22.E2067T
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22E16

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin

@[expose] noncomputable def E (L : Nat) : Nat := Fi22E16T.L L

@[expose] noncomputable def X (k : Nat) : Nat := Fi22ExtT.L (Nat.add 21 k)

@[expose] noncomputable def bit (m i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

theorem e16sz : CFSG.KS.Raw.szOK 3510 12 = true := by quickRfl

@[expose] noncomputable def fac (k m i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pidn 3510 12) (E (Nat.add (Nat.mul 4 k) i)) (bit m i)

@[expose] noncomputable def pr (k m : Nat) : Nat :=
  Fi22X.c (Fi22X.c (fac k m 0) (fac k m 1)) (Fi22X.c (fac k m 2) (fac k m 3))

@[expose] noncomputable def pt (k : Nat) : Nat := [0, 0, 1, 0, 4, 1].getD k 0

@[expose] noncomputable def im (k m x : Nat) : Nat :=
  pg 12 (mask 12) (fac k m 0) (pg 12 (mask 12) (fac k m 1)
    (pg 12 (mask 12) (fac k m 2) (pg 12 (mask 12) (fac k m 3) x)))

@[expose] noncomputable def e16dAt (k x : Nat) : Bool :=
  allN 16 (fun m => allN m (fun m' => Bool.not (Nat.beq (im k m' x) (im k m x))))

@[expose] noncomputable def e16d (k : Nat) : Bool := e16dAt k (pt k)

@[expose] noncomputable def e16sift (L : Nat) : Bool := Fi22X.siftP (E L)

theorem e16cnI : Fi22X.cn (pidn 3510 12) = true := by quickRfl

theorem e16cnE : allN 24 (fun L => Fi22X.cn (E L)) = true := by quickRfl

theorem e16cnX : allN 6 (fun k => Fi22X.cn (X k)) = true := by quickRfl

theorem e16perm : allN 24 (fun L => permOK 3510 12 (mask 12) (3510 * 12) (E L) (E L)) =
    true := by quickRfl

theorem e16sq : allN 24 (fun L => Nat.beq (Fi22X.c (E L) (E L)) (pidn 3510 12)) = true := by
  quickRfl

theorem e16t : allN 24 (fun L => Nat.beq (Fi22X.c (E L) (X (Nat.div L 4)))
    (Fi22X.c (X (Nat.div L 4)) (E L))) = true := by quickRfl

theorem e16cm : allN 24 (fun L => allN 4 (fun j =>
    Nat.beq (Fi22X.c (E L) (E (Nat.add (Nat.mul 4 (Nat.div L 4)) j)))
      (Fi22X.c (E (Nat.add (Nat.mul 4 (Nat.div L 4)) j)) (E L)))) = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22E16

#kc_each CertificateChecks.KernelSpor.Fi22E16.e16sift 0 24

#kc_each CertificateChecks.KernelSpor.Fi22E16.e16d 0 6

namespace CertificateChecks.KernelSpor.Fi22E16

#kc_forall_chunks S.all (fun L => e16sift L = true) 24 CertificateChecks.KernelSpor.Fi22E16.e16sift 1

#kc_forall_chunks D.all (fun k => e16d k = true) 6 CertificateChecks.KernelSpor.Fi22E16.e16d 1

end CertificateChecks.KernelSpor.Fi22E16

end
