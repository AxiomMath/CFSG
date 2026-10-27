module

public import Certificates.Kernel.He7223.Glue
public import Certificates.Data.Kernel.He7222.Good
public import CFSG.Certificates.Kernel.Misc.WordPtsSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelHe7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KC.HeChain CFSG.KC.WordPts CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.He CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CertificateChecks.KernelLC.HeFix CertificateChecks.KernelHe7223

theorem letT_icode (S SI : ℕ → ℕ) (z : ℤ) : letT S SI (icode z) = letP S SI z := by
  rcases z with k | k
  · change nIf(Nat.beq (Nat.land (Nat.add k k) 1) 0, S (Nat.sub (Nat.shiftRight (Nat.add k k) 1) 1),
      SI (Nat.sub (Nat.shiftRight (Nat.add k k) 1) 1)) = S (Nat.sub k 1)
    have h1 : Nat.land (Nat.add k k) 1 = 0 := by
      change (k + k) &&& 1 = 0
      rw [Nat.and_one_is_mod]
      omega
    have h2 : Nat.shiftRight (Nat.add k k) 1 = k := by
      change (k + k) >>> 1 = k
      rw [Nat.shiftRight_eq_div_pow]
      omega
    rw [h1, h2]
    rfl
  · change nIf(Nat.beq (Nat.land (Nat.succ (Nat.add (Nat.succ k) (Nat.succ k))) 1) 0,
      S (Nat.sub (Nat.shiftRight (Nat.succ (Nat.add (Nat.succ k) (Nat.succ k))) 1) 1),
      SI (Nat.sub (Nat.shiftRight (Nat.succ (Nat.add (Nat.succ k) (Nat.succ k))) 1) 1)) = SI k
    have h1 : Nat.land (Nat.succ (Nat.add (Nat.succ k) (Nat.succ k))) 1 = 1 := by
      change (k + 1 + (k + 1) + 1) &&& 1 = 1
      rw [Nat.and_one_is_mod]
      omega
    have h2 : Nat.shiftRight (Nat.succ (Nat.add (Nat.succ k) (Nat.succ k))) 1 = k + 1 := by
      change (k + 1 + (k + 1) + 1) >>> 1 = k + 1
      rw [Nat.shiftRight_eq_div_pow]
      omega
    rw [h1, h2]
    rfl

theorem letTI_icode (S SI : ℕ → ℕ) (z : ℤ) : letTI S SI (icode z) = letP SI S z := by
  rcases z with k | k
  · change nIf(Nat.beq (Nat.land (Nat.add k k) 1) 0, SI (Nat.sub (Nat.shiftRight (Nat.add k k) 1) 1),
      S (Nat.sub (Nat.shiftRight (Nat.add k k) 1) 1)) = SI (Nat.sub k 1)
    have h1 : Nat.land (Nat.add k k) 1 = 0 := by
      change (k + k) &&& 1 = 0
      rw [Nat.and_one_is_mod]
      omega
    have h2 : Nat.shiftRight (Nat.add k k) 1 = k := by
      change (k + k) >>> 1 = k
      rw [Nat.shiftRight_eq_div_pow]
      omega
    rw [h1, h2]
    rfl
  · change nIf(Nat.beq (Nat.land (Nat.succ (Nat.add (Nat.succ k) (Nat.succ k))) 1) 0,
      SI (Nat.sub (Nat.shiftRight (Nat.succ (Nat.add (Nat.succ k) (Nat.succ k))) 1) 1),
      S (Nat.sub (Nat.shiftRight (Nat.succ (Nat.add (Nat.succ k) (Nat.succ k))) 1) 1)) = S k
    have h1 : Nat.land (Nat.succ (Nat.add (Nat.succ k) (Nat.succ k))) 1 = 1 := by
      change (k + 1 + (k + 1) + 1) &&& 1 = 1
      rw [Nat.and_one_is_mod]
      omega
    have h2 : Nat.shiftRight (Nat.succ (Nat.add (Nat.succ k) (Nat.succ k))) 1 = k + 1 := by
      change (k + 1 + (k + 1) + 1) >>> 1 = k + 1
      rw [Nat.shiftRight_eq_div_pow]
      omega
    rw [h1, h2]
    rfl

theorem wpK_eq :
    ∀ {wd : List ℤ}, lettersOK gens3.length wd = true →
      ∀ x : Fin 8330, wpK 14 (mask 14) LU LUI wd x = (elt wd x : ℕ)
  | [], _, x => by
    change (x : ℕ) = (evalSignedWord gens3 [] x : ℕ)
    rw [evalSignedWord_nil']
    rfl
  | z :: wd, h, x => by
    obtain ⟨hz, hwd⟩ := letters_cons h
    change strictN (wpK 14 (mask 14) LU LUI wd x) (fun q => strictN (icode z)
      (fun c => pg 14 (mask 14) (letT LU LUI c) q)) = (evalSignedWord gens3 (z :: wd) x : ℕ)
    rw [strictN_eq', wpK_eq hwd x, strictN_eq', letT_icode, (letP_rep letRep_LU hz).1,
      evalSignedWord_cons' hz hwd, Equiv.Perm.mul_apply]
    rfl

theorem wpIK_eq :
    ∀ {wd : List ℤ}, lettersOK gens3.length wd = true →
      ∀ x : Fin 8330, wpIK 14 (mask 14) LU LUI wd x = ((elt wd)⁻¹ x : ℕ)
  | [], _, x => by
    change (x : ℕ) = ((evalSignedWord gens3 [])⁻¹ x : ℕ)
    rw [evalSignedWord_nil']
    rfl
  | z :: wd, h, x => by
    obtain ⟨hz, hwd⟩ := letters_cons h
    change strictN (icode z) (fun c => wpIK 14 (mask 14) LU LUI wd
      (pg 14 (mask 14) (letTI LU LUI c) x)) = ((evalSignedWord gens3 (z :: wd))⁻¹ x : ℕ)
    rw [strictN_eq', letTI_icode, (letP_rep letRep_LU hz).2]
    rw [wpIK_eq hwd, evalSignedWord_cons' hz hwd, mul_inv_rev, Equiv.Perm.mul_apply]
    rfl

end CertificateChecks.KernelHe7222

end
