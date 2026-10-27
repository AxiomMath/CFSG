module

public import Certificates.Data.Kernel.L34Cov.Walk
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Data.F4a
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Data.F4b

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration

@[expose] noncomputable def cvId (w : List (Fin 2 × Bool)) (c₁ c₂ c₃ : Nat) : Bool :=
  cvIdOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab (w.map letterCode) c₁ c₂ c₃

theorem vt_k : vtOK VT = true := by decide +kernel

theorem vt_neg : (!vtOK (Nat.add VT 1)) = true := by decide +kernel

theorem zOne_k : cvId zOne 1 0 0 = true := by decide +kernel

theorem zTwo_k : cvId zTwo 0 1 0 = true := by decide +kernel

theorem zThree_k : cvId zThree 0 0 1 = true := by decide +kernel

theorem zz_k : cvId (wpow zOne 2 ++ wpow zTwo 2) 2 2 0 = true := by decide +kernel

theorem cover_k : cvId ((0, false) :: commWords (coverPairs 0)) 0 0 0 = true ∧
    cvId ((1, false) :: commWords (coverPairs 1)) 0 0 0 = true := by decide +kernel

theorem zOne_neg : (!cvId zOne 2 0 0) = true := by decide +kernel

theorem zTwo_neg : (!cvId zTwo 2 3 0) = true := by decide +kernel

theorem zThree_neg : (!cvId zThree 0 0 0) = true := by decide +kernel

end CertificateChecks.KernelL34Cov

end
