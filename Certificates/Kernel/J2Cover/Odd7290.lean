module

public import Certificates.Kernel.J2Cover.ModelsBind
public import Certificates.Kernel.J2Cover.M22Lk
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverOddNative
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J2ModelsGen
public import Certificates.Kernel.J2Cover.M22Blocks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover.Odd7290

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelJ2Cover
open CFSG.ComponentClassification.J2Cover.Models

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 315 9 (mask 9) p q

@[expose] noncomputable def I0 : Nat := pidn 315 9

@[expose] noncomputable def G3 : Nat := wordP oddW3

@[expose] noncomputable def G3s : Nat := pc G3 G3

@[expose] noncomputable def G5 : Nat := wordP oddW5

@[expose] noncomputable def G5s : Nat := pc G5 G5

@[expose] noncomputable def G5i : Nat := pc G5s G5s

@[expose] noncomputable def oddK (k : Nat) : Bool :=
  !oddWidxB k ||
    (decide (nth 0 oddC3 k < 128) && oddWidxB (nth 0 oddC3 k) &&
      Nat.beq (pc (pc G3 (ELT k)) G3s) (ELT (nth 0 oddC3 k)) &&
      decide (nth 0 oddC3i k < 128) && oddWidxB (nth 0 oddC3i k) &&
      Nat.beq (pc (pc G3s (ELT k)) G3) (ELT (nth 0 oddC3i k)) &&
      decide (nth 0 oddC5 k < 128) && oddWidxB (nth 0 oddC5 k) &&
      Nat.beq (pc (pc G5 (ELT k)) G5i) (ELT (nth 0 oddC5 k)) &&
      decide (nth 0 oddC5i k < 128) && oddWidxB (nth 0 oddC5i k) &&
      Nat.beq (pc (pc G5i (ELT k)) G5) (ELT (nth 0 oddC5i k)))

theorem k3290 : Nat.beq (pc G3 G3s) I0 = true := by quickRfl

theorem k3n7290 : (!Nat.beq G3 I0) = true := by quickRfl

theorem k5290 : Nat.beq (pc G5 G5i) I0 = true := by quickRfl

theorem k5n7290 : (!Nat.beq G5 I0) = true := by quickRfl

theorem kc37290 : Nat.beq (pc G3 (ELT 4)) (pc (ELT 4) G3) = true := by quickRfl

theorem kc57290 : Nat.beq (pc G5 (ELT 4)) (pc (ELT 4) G5) = true := by quickRfl

theorem kW7290 : allN 128 oddK = true := by quickRfl

theorem kF7290 : allN 128 (fun i => mtK i i != 4 || (fRK i).testBit i) = true := by quickRfl

end CertificateChecks.KernelJ2Cover.Odd7290

end
