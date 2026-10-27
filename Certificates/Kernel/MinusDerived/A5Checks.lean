module

public import Certificates.Kernel.MinusDerived.A5
public import Certificates.Kernel.MinusDerived.Local
public import Certificates.Kernel.MinusEnum.Data
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.PermPinK
public import Certificates.Data.Kernel.Misc.PermWit
public import CFSG.Certificates.Kernel.LocalCompUnpack

public section

namespace CertificateChecks.KernelMinusA5

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
  CFSG.KC.PermWit CFSG.KC.PermPinK CertificateChecks.KernelMinusL

@[expose] noncomputable def pa (p q : ℕ) : ℕ := pcomp 65 7 (mask 7) p q

@[expose] noncomputable def ia : ℕ := pidn 65 7

@[expose] noncomputable def gOKF (G : ℕ → ℕ) (k : ℕ) : Bool :=
  permOK 65 7 (mask 7) (Nat.mul 65 7) (G k) (pinvS 65 7 (mask 7) (G k))

@[expose] noncomputable def skF : List ℕ := (List.range 60).map KF

theorem kOrdA : (Nat.beq (pa (pa (LX 0) (LX 0)) (pa (LX 0) (LX 0))) ia &&
    !Nat.beq (pa (LX 0) (LX 0)) ia) = true := by decide +kernel

theorem kSqB : Nat.beq (pa (LX 1) (LX 1)) ia = true := by decide +kernel

theorem kConjB : Nat.beq (pa (pa (LX 1) (LX 0)) (LX 1)) (pa (pa (LX 0) (LX 0)) (LX 0)) = true := by
  decide +kernel

theorem kNotMem : (!Nat.beq (LX 1) ia && !Nat.beq (LX 1) (LX 0) &&
    !Nat.beq (LX 1) (pa (LX 0) (LX 0)) && !Nat.beq (LX 1) (pa (pa (LX 0) (LX 0)) (LX 0))) = true := by
  decide +kernel

theorem kComm : allN 2 (fun k => Nat.beq (pa (LX (k + 2)) (KernelMinusEnum.ME.G 0))
    (pa (KernelMinusEnum.ME.G 0) (LX (k + 2)))) = true := by decide +kernel

theorem kNumsF : (Nat.beq SF.ng 2 && Nat.beq SF.N 60) = true := by decide +kernel

theorem kBindF : (Nat.beq minusA5Gens.size 2 &&
    allN 2 fun k => bindArrK minusA5Gens[k]! 65 7 (SF.G k)) = true := by decide +kernel

theorem kPermF : allN 2 (gOKF SF.G) = true := by decide +kernel

theorem kPermTF : allN 60 (gOKF SF.T) = true := by decide +kernel

theorem kKF : keysSK 65 7 minusBase SF.N SF.T skF = true := by decide +kernel

theorem kTreeF : allN 60 (fun k => Nat.beq (SF.T k) (pidn 65 7) ||
    allN 60 (ctreePt 65 7 60 k SF.T (WF k))) = true := by decide +kernel

theorem kT0F : Nat.beq (SF.T 0) (pidn 65 7) = true := by decide +kernel

end CertificateChecks.KernelMinusA5

end
