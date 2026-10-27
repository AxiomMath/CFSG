module

public import Certificates.Kernel.Sporadic.OddCore.J2Cn
public import Certificates.Data.Kernel.Ivk8Cent
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelIvk8J2

open CFSG.KC.Enum CFSG.KS.Ivk8Cent CertificateChecks.KernelSpor

@[expose] noncomputable def lt (l : Nat) : Nat :=
  nIf(Nat.beq l 0, J2P.S 0, nIf(Nat.beq l 1, J2P.S 1, nIf(Nat.beq l 2, J2P.SI 0, J2P.SI 1)))

@[expose] def wA : List Nat :=
  [1, 2, 1, 0, 3, 3, 0, 3, 2, 2, 3, 2, 3, 0, 3, 2, 3, 2, 2, 2, 3, 3, 3, 2, 2, 3]

@[expose] def wB : List Nat :=
  [1, 2, 2, 1, 2, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 1, 2, 1, 2, 3, 3]

@[expose] def wC : List Nat :=
  [3, 2, 2, 2, 1, 2, 3, 0, 1, 2, 1, 0, 1, 0, 1, 1, 2, 3, 0, 3, 2, 1, 2, 2, 2, 3, 2, 1]

@[expose] def c1 : List Nat :=
  [0, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 1, 0, 3, 0,
    1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0]

@[expose] def c1i : List Nat :=
  [2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 1, 0,
    3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2]

@[expose] def c2 : List Nat :=
  [1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2,
    3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1,
    0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1,
    0]

@[expose] def c2i : List Nat :=
  [2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1,
    2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0,
    1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2,
    3]

@[expose] def c3 : List Nat :=
  [2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3,
    2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3,
    2, 3]

@[expose] def c3i : List Nat :=
  [1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0,
    3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0,
    3, 0]

@[expose] noncomputable def wH (k : Nat → Nat → Nat → List Nat → Bool) : Bool :=
  withH 315 9 lt wA wB wC k

@[expose] noncomputable def chkC (c ci : List Nat) (cnt : Nat) (T : Nat → Nat) : Bool :=
  wH fun _ _ _ hs => strictB (evW 315 9 lt c) fun x => strictB (evW 315 9 lt ci) fun xi =>
    chkKP 315 9 x xi cnt T hs

theorem ch5246_h : hOK 315 9 lt wA wB wC = true := by
  quickRfl

theorem ch5246_tE : wH (fun C AB ABC _ =>
    bAnd(conjOK 315 9 (evW 315 9 lt c1) (evW 315 9 lt c1i) (J2CentT.F 17) C,
    bAnd(conjOK 315 9 (evW 315 9 lt c2) (evW 315 9 lt c2i) (J2CentT.F 31) AB,
      conjOK 315 9 (evW 315 9 lt c3) (evW 315 9 lt c3i) (J2CentT.F 17) ABC))) = true := by
  quickRfl

theorem ch5246_t3a : chkC c2 c2i J2Q3a.cnt J2Q3a.T = true := by
  quickRfl

theorem ch5246_t2c1 : chkC c1 c1i J2Q2c.cnt J2Q2c.T = true := by
  quickRfl

theorem ch5246_t2c3 : chkC c3 c3i J2Q2c.cnt J2Q2c.T = true := by
  quickRfl

end CertificateChecks.KernelIvk8J2

end
