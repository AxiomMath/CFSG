module

public import Certificates.Kernel.LocalComp.WittData
public import Certificates.Kernel.LocalComp.M22Hexads
public import CFSG.Certificates.Kernel.WittCntSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.WCnt CFSG.KS.PCnt

@[expose] def wB : List Bool := [true, false, true, true, false, true, true, true, false, true,
  false, true, true, true, false, true, true, true, false, true, false, true, true]

@[expose] def wZ : List Bool := [false, true, false, true, true, true, false, true, false, true,
  true, false, true, false, true, false, true, false, true, true, false, true, false]

@[expose] def wW : List Bool := [true, false, true, false, true, false, true, false, true, false,
  true, false, true, true, true, false, true, false, true, false, true, true, false, true, true,
  true]

@[expose] def wY : List Bool := [true, false, true, true, false, true, false, true, true, false,
  true, false, true, true, false, true, true, true, false]

@[expose] def wO1 : List Bool := [true, false, true, false, true, true, false, true, false, true,
  false, true, true, false, true, false, true, false]

@[expose] def wO2 : List Bool := [false, true, false, true, false, true, false, true, false, true,
  false, true, true, true, false, true, false, true, true, false, true]

@[expose] def wO3 : List Bool := [true, false, true, false, true, true, true, false, true, true,
  true, false, true, false, true, false, true, false, true, true]

theorem pk_wB : pkw 5 (wordPerm wB) = dB := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_wZ : pkw 5 (wordPerm wZ) = dZ := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_wW : pkw 5 (wordPerm wW) = dW := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_wY : pkw 5 (wordPerm wY) = dY := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_wO1 : pkw 5 (wordPerm wO1) = dO1 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_wO2 : pkw 5 (wordPerm wO2) = dO2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem pk_wO3 : pkw 5 (wordPerm wO3) = dO3 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem app_of_pk {d : Equiv.Perm (Fin 22)} {D : Nat} (h : pkw 5 d = D) (i : Fin 22) :
    (d i).val = pt D i.val := by
  rw [← h, pt_pkw]

theorem mul_apply_of_pk {d : Equiv.Perm (Fin 22)} {D : Nat} (h : pkw 5 d = D)
    (σ : Equiv.Perm (Fin 22)) {e i : Fin 22} (he : pt D e.val = i.val) : (σ * d) e = σ i := by
  rw [Equiv.Perm.mul_apply]
  exact congrArg σ (Fin.ext ((app_of_pk h e).trans he))

end CertificateChecks.KernelLC.Witt

end
