module

public import Certificates.Kernel.Misc.Perm.HS100.TData
public import Certificates.Kernel.Misc.Perm.HS100.NChecks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KC.Misc.ArrEnum (permB memK fixK)
open CFSG.KC.LQT.P (anyN)
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.S0 (cK Z0)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

@[expose] noncomputable def ET (j i : Nat) : Nat :=
  if j = 0 then E0.T i else if j = 1 then E1.T i else if j = 2 then E2.T i else
  if j = 3 then E3.T i else if j = 4 then E4.T i else if j = 5 then E5.T i else
  if j = 6 then E6.T i else E7.T i

@[expose] noncomputable def isInvK (p : Nat) : Bool :=
  Nat.beq (pcomp 100 7 (mask 7) p p) (pidn 100 7) && !(Nat.beq p (pidn 100 7))

@[expose] noncomputable def inK2 (a b : Nat) : Bool :=
  Nat.beq b (pidn 100 7) || Nat.beq b Z0 || Nat.beq b a || Nat.beq b (pcomp 100 7 (mask 7) Z0 a)

@[expose] noncomputable def inK3 (a b c : Nat) : Bool :=
  inK2 a c || Nat.beq c (pcomp 100 7 (mask 7) b (pidn 100 7)) ||
    Nat.beq c (pcomp 100 7 (mask 7) b Z0) || Nat.beq c (pcomp 100 7 (mask 7) b a) ||
    Nat.beq c (pcomp 100 7 (mask 7) b (pcomp 100 7 (mask 7) Z0 a))

@[expose] noncomputable def inSome (a b c : Nat) : Bool :=
  anyN 8 fun j => memK 16 (ET j) a && memK 16 (ET j) b && memK 16 (ET j) c

@[expose] noncomputable def uniqAt (ja : Nat) : Bool :=
  strictB (TT.T (TTI ja)) fun a =>
    Nat.beq a (pidn 100 7) || Nat.beq a Z0 ||
      allN 87 fun jb => strictB (TT.T (TTI jb)) fun b =>
        !(cK a b) || inK2 a b ||
          allN 87 fun jc => strictB (TT.T (TTI jc)) fun c =>
            !(cK a c) || !(cK b c) || inK3 a b c || inSome a b c

theorem perms : (allN 3 (fun k => permB 100 7 (TX.F k)) && allN 32 (fun k => permB 100 7 (EA.F k)))
    = true := by quickRfl

theorem nums : (Nat.beq TT.ng 3 && Nat.beq TT.N 512 && allN 3 (fun k => Nat.beq (TT.G k) (TX.F k)) &&
    Nat.beq E0.ng 4 && Nat.beq E0.N 16 && Nat.beq E1.ng 4 && Nat.beq E1.N 16 &&
    Nat.beq E2.ng 4 && Nat.beq E2.N 16 && Nat.beq E3.ng 4 && Nat.beq E3.N 16 &&
    Nat.beq E4.ng 4 && Nat.beq E4.N 16 && Nat.beq E5.ng 4 && Nat.beq E5.N 16 &&
    Nat.beq E6.ng 4 && Nat.beq E6.N 16 && Nat.beq E7.ng 4 && Nat.beq E7.N 16) = true := by quickRfl

theorem ebinds : (allN 4 (fun k => Nat.beq (E0.G k) (EA.F k)) &&
    allN 4 (fun k => Nat.beq (E1.G k) (EA.F (4 + k))) &&
    allN 4 (fun k => Nat.beq (E2.G k) (EA.F (8 + k))) &&
    allN 4 (fun k => Nat.beq (E3.G k) (EA.F (12 + k))) &&
    allN 4 (fun k => Nat.beq (E4.G k) (EA.F (16 + k))) &&
    allN 4 (fun k => Nat.beq (E5.G k) (EA.F (20 + k))) &&
    allN 4 (fun k => Nat.beq (E6.G k) (EA.F (24 + k))) &&
    allN 4 (fun k => Nat.beq (E7.G k) (EA.F (28 + k)))) = true := by quickRfl

theorem keys : keysSK 100 7 zasTKeys TT.N TT.T ((List.range 512).map TTK) = true := by quickRfl

theorem invs : (allN 87 (fun j => Nat.blt (TTI j) 512 && isInvK (TT.T (TTI j))) &&
    allN 86 (fun j => Nat.blt (TTI j) (TTI (j + 1))) &&
    allN 512 (fun i => !(isInvK (TT.T i)) || anyN 87 fun j => Nat.beq (TTI j) i)) = true := by
  quickRfl

theorem tperm : allN 512 (fun i => permB 100 7 (TT.T i)) = true := by quickRfl

theorem zmem :allN 8 (fun j => memK 16 (ET j) Z0) = true := by quickRfl

theorem fixes : allN 8 (fun j => Nat.beq j 0 || Nat.beq j 5 ||
    anyN 16 fun i => !(Nat.beq (ET j i) (pidn 100 7)) && !(Nat.beq (fixK 100 7 (ET j i)) (fixK 100 7 Z0)))
    = true := by quickRfl

theorem conjE : anyN 512 (fun i => allN 4 fun k => memK 16 (ET 5) (N.pZ (TT.T i) (EA.F k))) = true := by
  quickRfl

theorem uniq : allN 87 uniqAt = true := by quickRfl

end CertificateChecks.KernelMisc.HS100.T

end
