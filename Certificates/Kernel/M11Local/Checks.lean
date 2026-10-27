module

public import Certificates.Data.Kernel.M11Local

public section

namespace CertificateChecks.KernelM11Local

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.KG CFSG.KC.M11L

@[expose] def xK : Nat := 5887001347886112

@[expose] def yK : Nat := 6833572453553184

@[expose] def sK : Nat := 3562496302714881

@[expose] def aK : Nat := 3420860021279008

@[expose] def bK : Nat := 11576764645055619

@[expose] def wx : List Bool :=
  [true, false, true, true, false, true, true, false, true, true, true, false, true, true, true,
    false, true, true, true]

@[expose] def wy : List Bool :=
  [true, false, true, false, true, false, true, true, false, true, true, false, true, false, true,
    false, true, true, false, true]

@[expose] def ws : List Bool := [true, false, true, true, false, true, false, true]

theorem m11K_ok : m11K xK yK sK aK bK wx wy ws = true := by decide +kernel

end CertificateChecks.KernelM11Local

end
