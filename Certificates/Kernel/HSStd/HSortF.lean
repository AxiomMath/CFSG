module

public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CertificateChecks.KernelHSStd.HSortF

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def hsortPtKF (n w m cnt : Nat) (T HS HSI : Nat → Nat) (i : Nat) : Bool :=
  strictB (r32 HS i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 HSI s) i,
    bIf(Nat.blt (Nat.succ i) cnt,
      strictB (r32 HS (Nat.succ i)) (fun s' => Nat.blt (hkeyK n w m (T s)) (hkeyK n w m (T s'))),
      true))))

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem hsortPtK_F : hsortPtK = hsortPtKF := by
  funext n w m cnt T HS HSI i
  unfold hsortPtK hsortPtKF
  simp only [strictB_eq]

end CertificateChecks.KernelHSStd.HSortF

end
