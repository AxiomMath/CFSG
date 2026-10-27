module

public import Certificates.Kernel.LocalComp.C589102Chk
public import Certificates.Kernel.LocalComp.C589102E16
public import Certificates.Kernel.LocalComp.L34Cert
public import Certificates.Data.S1277Kt
public import CFSG.Certificates.Kernel.LocalCompPinSound
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.C589102

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.PSL3Four.Native CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X
open Certificates.Data.S1277Kt

theorem pinOS : PinO 42 6 gensS (r₁T ()) 315 3 315 11 (RP 0) L34R.G GI L34SO.T L34SO.E L34SO.S
    L34SO.SI :=
  ⟨L34Cert.bindS.1, L34Cert.bindS.2, L34Cert.r1_eq, k589102orb, le_refl _⟩

theorem orbitS_ok : ktOrbitSOK () = true := by
  obtain ⟨h1, h2⟩ := orbit_sound pinOS
  simp only [ktOrbitSOK, ktOrbitS, ktR1]
  rw [h2, h1, size_pts]
  rfl

theorem kBindE1 : (Nat.beq ktGenE1.size K589E1.ng &&
    allN K589E1.ng fun k => bindArrK ktGenE1[k]! 42 6 (K589E1.G k)) = true := by quickRfl

theorem kBindE2 : (Nat.beq ktGenE2.size K589E2.ng &&
    allN K589E2.ng fun k => bindArrK ktGenE2[k]! 42 6 (K589E2.G k)) = true := by quickRfl

theorem kBindB1 : (Nat.beq ktGenB1.size K589B1.ng &&
    allN K589B1.ng fun k => bindArrK ktGenB1[k]! 42 6 (K589B1.G k)) = true := by quickRfl

theorem kBindB2 : (Nat.beq ktGenB2.size K589B2.ng &&
    allN K589B2.ng fun k => bindArrK ktGenB2[k]! 42 6 (K589B2.G k)) = true := by quickRfl

theorem hE1 : enumOK 42 ktGenE1 (enumBFS 42 ktGenE1 16) = true ∧
    (enumBFS 42 ktGenE1 16).tabs = Array.ofFn (n := K589E1.N) fun i => unpack 42 6 (K589E1.T i.val) :=
  CFSG.KC.LocalComp.Pin.enumBFS_of_bfsK (binds_of_check kBindE1).1 (binds_of_check kBindE1).2
    K589E1.ok (by decide)

theorem hE2 : enumOK 42 ktGenE2 (enumBFS 42 ktGenE2 16) = true ∧
    (enumBFS 42 ktGenE2 16).tabs = Array.ofFn (n := K589E2.N) fun i => unpack 42 6 (K589E2.T i.val) :=
  CFSG.KC.LocalComp.Pin.enumBFS_of_bfsK (binds_of_check kBindE2).1 (binds_of_check kBindE2).2
    K589E2.ok (by decide)

theorem hB1 : enumOK 42 ktGenB1 (enumBFS 42 ktGenB1 16) = true ∧
    (enumBFS 42 ktGenB1 16).tabs = Array.ofFn (n := K589B1.N) fun i => unpack 42 6 (K589B1.T i.val) :=
  CFSG.KC.LocalComp.Pin.enumBFS_of_bfsK (binds_of_check kBindB1).1 (binds_of_check kBindB1).2
    K589B1.ok (by decide)

theorem hB2 : enumOK 42 ktGenB2 (enumBFS 42 ktGenB2 16) = true ∧
    (enumBFS 42 ktGenB2 16).tabs = Array.ofFn (n := K589B2.N) fun i => unpack 42 6 (K589B2.T i.val) :=
  CFSG.KC.LocalComp.Pin.enumBFS_of_bfsK (binds_of_check kBindB2).1 (binds_of_check kBindB2).2
    K589B2.ok (by decide)

end CertificateChecks.KernelLC.C589102

end
