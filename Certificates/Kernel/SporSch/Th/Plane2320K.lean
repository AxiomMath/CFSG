
module

public import Certificates.Kernel.SporSch.Th.UA2325
public import Certificates.Kernel.SporSch.Th.Key2311Base
public import Certificates.Kernel.SporSch.Th.GenChain
public import Certificates.Kernel.Co1B.GenTri2045
public import CFSG.Sporadic.ThSchreier.TransporterBase
meta import CFSG.Sporadic.ThSchreier.TransporterBase
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.ThSeedB CFSG.Sporadic.Th.Native.seedB
#kss_v4rows CertificateChecks.KernelSporSch.ThB CFSG.Sporadic.Th.Max3.rowsB

namespace CertificateChecks.KernelSporSch.ThPlane

open CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier

meta def bbArr : Array V4 := mulRows CFSG.Sporadic.Th.Max3.rowsB CFSG.Sporadic.Th.Max3.rowsB

meta def ivw : List Int := invWord transporterWord

end CertificateChecks.KernelSporSch.ThPlane

#kss_v4rows CertificateChecks.KernelSporSch.ThBB CertificateChecks.KernelSporSch.ThPlane.bbArr

#kss_suffix CertificateChecks.KernelSporSch.ThVI CertificateChecks.KernelSporSch.ThA
  CertificateChecks.KernelSporSch.ThBB CFSG.Sporadic.Th.Max3.rowsA
  CertificateChecks.KernelSporSch.ThPlane.bbArr CertificateChecks.KernelSporSch.ThPlane.ivw

namespace CertificateChecks.KernelSporSch.ThPlane

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThUA (UB)
open CertificateChecks.KernelSporSch.ThKey (C1 C2)

theorem seedB_ok : thPayK ThB ThSeedB.chars = true := by quickRfl

@[expose] noncomputable def fBB (i : Nat) : Bool := Nat.beq (vmT ThB (ThB i)) (ThBB i)

@[expose] noncomputable def fBBs (q : Nat) : Bool := allBlk (Nat.mul 31 q) fBB 31

end CertificateChecks.KernelSporSch.ThPlane

#kc_slices CertificateChecks.KernelSporSch.ThPlane.BBs CertificateChecks.KernelSporSch.ThPlane.fBBs 8

namespace CertificateChecks.KernelSporSch.ThPlane

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThUA (UB)
open CertificateChecks.KernelSporSch.ThKey (C1 C2)

theorem ltB : allN 248 (fun i => Nat.blt (ThB i) (Nat.shiftLeft 1 248)) = true := by quickRfl
theorem ltBB : allN 248 (fun i => Nat.blt (ThBB i) (Nat.shiftLeft 1 248)) = true := by quickRfl
theorem ltSS : allN 8680 (fun i => Nat.blt (ThVI.SS i) (Nat.shiftLeft 1 248)) = true := by quickRfl

theorem wc : wcFrom ThVI.LC (invWord transporterWord) 0 = true := by quickRfl
theorem last : allN 248 (fun i => Nat.beq (slice ThVI.SS 34 i) (letRow ThVI.LC ThA ThBB 34 i)) =
    true := by quickRfl

@[expose] noncomputable def KA : Nat := canonN C1 C2 % 2 ^ 256
@[expose] noncomputable def KB : Nat := canonN C1 C2 / 2 ^ 256
@[expose] noncomputable def IA : Nat := vmT (slice ThVI.SS 0) (canonN C1 C2 % 2 ^ 256)
@[expose] noncomputable def IB : Nat := vmT (slice ThVI.SS 0) (canonN C1 C2 / 2 ^ 256)
@[expose] noncomputable def SU : Nat :=
  canonN (vmT (slice ThVI.SS 0) (canonN C1 C2 % 2 ^ 256))
    (vmT (slice ThVI.SS 0) (canonN C1 C2 / 2 ^ 256)) % 2 ^ 256
@[expose] noncomputable def SV : Nat :=
  canonN (vmT (slice ThVI.SS 0) (canonN C1 C2 % 2 ^ 256))
    (vmT (slice ThVI.SS 0) (canonN C1 C2 / 2 ^ 256)) / 2 ^ 256

theorem kA : Nat.blt KA (Nat.shiftLeft 1 248) = true := by quickRfl
theorem kB : Nat.blt KB (Nat.shiftLeft 1 248) = true := by quickRfl
theorem kIA : Nat.blt IA (Nat.shiftLeft 1 248) = true := by quickRfl
theorem kIB : Nat.blt IB (Nat.shiftLeft 1 248) = true := by quickRfl
theorem kSU : Nat.blt SU (Nat.shiftLeft 1 248) = true := by quickRfl
theorem kSV : Nat.blt SV (Nat.shiftLeft 1 248) = true := by quickRfl
theorem uU : Nat.beq (Nat.shiftRight (vmT (UB 1) SU) 120) 0 = true := by quickRfl
theorem uV : Nat.beq (Nat.shiftRight (vmT (UB 1) SV) 120) 0 = true := by quickRfl
theorem kC1 : Nat.blt C1 (Nat.shiftLeft 1 248) = true := by quickRfl
theorem kC2 : Nat.blt C2 (Nat.shiftLeft 1 248) = true := by quickRfl

end CertificateChecks.KernelSporSch.ThPlane

end
