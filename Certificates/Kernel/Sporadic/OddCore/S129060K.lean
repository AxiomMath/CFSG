module

public import Certificates.Kernel.Sporadic.OddCore.S129060D
public import Certificates.Kernel.Sporadic.Suz.Order2306
public import Certificates.Data.Kernel.SporSch.Kappa
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S129060

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CertificateChecks.KernelSpor

@[expose] noncomputable def fv (P i : Nat) : Nat := pg 11 (mask 11) P i

@[expose] noncomputable def itr (d P p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ q => fv P q) d

@[expose] noncomputable def A (k : Nat) : Nat := S1290A k

@[expose] noncomputable def AI (k : Nat) : Nat := S1290A (Nat.add 6 k)

@[expose] noncomputable def ev (e₀ e₁ e₂ e₃ e₄ p : Nat) : Nat :=
  itr e₀ (A 0) (itr e₁ (A 1) (itr e₂ (A 2) (itr e₃ (A 3) (itr e₄ (A 4) p))))

@[expose] noncomputable def ex (j i : Nat) : Nat := pg 2 (mask 2) (S1290E j) i

@[expose] noncomputable def evE (j p : Nat) : Nat := ev (ex j 0) (ex j 1) (ex j 2) (ex j 3) (ex j 4) p

@[expose] noncomputable def wt (e₀ e₁ e₂ e₃ e₄ : Nat) : Nat :=
  pg 11 (mask 11) (S1290W 0) (Nat.add e₀ (Nat.add (Nat.mul 3 e₁) (Nat.add (Nat.mul 9 e₂)
    (Nat.add (Nat.mul 27 e₃) (Nat.mul 81 e₄)))))

@[expose] noncomputable def pK : Bool :=
  allN 6 fun k => permOK 1782 11 (mask 11) (1782 * 11) (A k) (AI k)

@[expose] noncomputable def mK : Bool := allN 6 fun k => Suz2306.sift (A k)

@[expose] noncomputable def cK : Bool :=
  allN 5 fun j => allN 1782 fun p => Nat.beq (itr 3 (A j) p) p

@[expose] noncomputable def abK : Bool :=
  allN 5 fun i => allN 5 fun j => allN 1782 fun p =>
    Nat.beq (fv (A i) (fv (A j) p)) (fv (A j) (fv (A i) p))

@[expose] noncomputable def gK : Bool := allN 1782 fun p => Nat.beq (itr 11 (A 5) p) p

@[expose] noncomputable def nK : Bool :=
  allN 5 fun j => allN 1782 fun p => Nat.beq (fv (A 5) (fv (A j) (fv (AI 5) p))) (evE j p)

@[expose] noncomputable def wK : Bool :=
  allN 3 fun e₀ => allN 3 fun e₁ => allN 3 fun e₂ => allN 3 fun e₃ => allN 3 fun e₄ =>
    bIf(Nat.beq (Nat.add e₀ (Nat.add e₁ (Nat.add e₂ (Nat.add e₃ e₄)))) 0, true,
      strictB (wt e₀ e₁ e₂ e₃ e₄) fun q =>
        bAnd(Nat.blt q 1782, bIf(Nat.beq (ev e₀ e₁ e₂ e₃ e₄ q) q, false, true)))

@[expose] noncomputable def ncK : Bool :=
  anyN 1782 fun p => bIf(Nat.beq (fv (A 5) (fv (A 0) (fv (AI 5) p))) (fv (A 0) p), false, true)

theorem pOK : pK = true := by quickRfl
theorem mOK : mK = true := by quickRfl
theorem cOK : cK = true := by quickRfl
theorem abOK : abK = true := by quickRfl
theorem gOK : gK = true := by quickRfl
theorem nOK : nK = true := by quickRfl
theorem wOK : wK = true := by quickRfl
theorem ncOK : ncK = true := by quickRfl

end CertificateChecks.KernelSpor.S129060

end
