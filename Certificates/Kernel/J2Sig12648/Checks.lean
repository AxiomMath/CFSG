module

public import Certificates.Data.Kernel.J2Sig12648
public import Certificates.Kernel.J2Sig12648.Data
public import Certificates.Kernel.Misc.Perm.J2EnumData
public import Certificates.Data.Kernel.Misc.PermClos
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelJ2Sig

open CFSG.KC.Enum CFSG.KC.J2Sig CFSG.KC.ConjRec
open CertificateChecks.KernelMisc.J2C3 (X Y Z I)
open CFSG.KC.Misc.Clos (allR)

@[expose] noncomputable def X2 : Nat := m9 X X

@[expose] noncomputable def Y2 : Nat := m9 Y Y

@[expose] noncomputable def cjG (k : Nat) : Nat := nIf(Nat.beq k (nat_lit 0), I, nIf(Nat.beq k (nat_lit 1), Y2, Y))
@[expose] noncomputable def cjGI (k : Nat) : Nat := nIf(Nat.beq k (nat_lit 0), I, nIf(Nat.beq k (nat_lit 1), Y, Y2))

@[expose] noncomputable def zC (c : Nat) : Bool :=
  allR (Nat.mul (nat_lit 90) c) (nat_lit 90) fun k => zK X X2 X2 X I VV W k
    (CertificateChecks.KernelMisc.J2C3.CzP.F k)

@[expose] noncomputable def wC (k : Nat) : Bool :=
  allR (nat_lit 0) (nat_lit 36) fun i =>
    wK I (cjG k) (cjGI k) VV (Nat.mul (nat_lit 3) k) (CFSG.KS.lget
      CertificateChecks.KernelMisc.J2En.CaP i)

end CertificateChecks.KernelJ2Sig

#kc_each CertificateChecks.KernelJ2Sig.zC 0 12
#kc_each CertificateChecks.KernelJ2Sig.wC 0 3

namespace CertificateChecks.KernelJ2Sig

open CFSG.KC.Enum CFSG.KC.J2Sig CFSG.KC.ConjRec
open CertificateChecks.KernelMisc.J2C3 (X Y Z I)
open CFSG.KC.Misc.Clos (allR)

theorem ch12648cj : ∀ k < 3, Nat.beq (m9 (cjG k) (m9 X (cjGI k)))
    (m9 (nIf(Nat.beq k (nat_lit 0), I, nIf(Nat.beq k (nat_lit 1), Z, m9 Z Z))) X) = true ∧
    Nat.beq (m9 (cjG k) (cjGI k)) I = true := by decide +kernel

theorem ch12648neg : zK X X2 X2 X I VV 0 7 (CertificateChecks.KernelMisc.J2C3.CzP.F 7) = false ∧
    allR 0 36 (fun i => wK I I I VV 3 (CFSG.KS.lget
      CertificateChecks.KernelMisc.J2En.CaP i)) = false := by
  constructor <;> decide +kernel

end CertificateChecks.KernelJ2Sig
