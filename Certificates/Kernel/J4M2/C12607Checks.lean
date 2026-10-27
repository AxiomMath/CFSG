module

public import Certificates.Kernel.SporSch.J4S11.Checks
public import Certificates.Kernel.J4Q.QT2AData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4GamData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Gam

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KC.Loop CFSG.KD.J4Q CFSG.KS.SporSch.J4B
  CertificateChecks.KernelSporSch.J4E7 CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

@[expose] def rowsOK (X : Array Nat) : Bool :=
  X.size == 112 && X.toList.all fun n => Nat.blt n (2 ^ 112)

@[expose] noncomputable def pk (X : Array Nat) : Nat :=
  (List.range 112).foldr (fun i acc => Nat.lor (Nat.shiftLeft (X.getD i 0) (128 * i)) acc) 0

@[expose] noncomputable def Z0 : Nat := pk gamZ0

@[expose] noncomputable def Z0P : Nat × Nat := (Z0, Z0)

@[expose] noncomputable def HP : Nat × Nat :=
  (wFK c rm one A A B Bi gamWord one, wSK c rm one A A B Bi gamWord one)

@[expose] noncomputable def JP : Nat × Nat := pP H2 20

@[expose] noncomputable def GP : Nat × Nat := mP (pP (mP Z0P (mP (mP HP JP) (iP HP))) 6) HP

@[expose] noncomputable def cjP (p : Nat × Nat) : Nat × Nat := mP (mP GP p) (iP GP)

@[expose] noncomputable def C1P : Nat × Nat := mP (pP (V 4) 10) H1

@[expose] noncomputable def GA : Nat × Nat := (pk gamAFwd, pk gamABwd)

@[expose] noncomputable def GB : Nat × Nat := (pk gamBFwd, pk gamBBwd)

@[expose] noncomputable def GZ : Nat × Nat := (pk gamZFwd, pk gamZBwd)

theorem rows_ok : (rowsOK gamZ0 && rowsOK gamAFwd && rowsOK gamABwd && rowsOK gamBFwd &&
    rowsOK gamBBwd && rowsOK gamZFwd && rowsOK gamZBwd) = true := by quickRfl

theorem z0_chk : Nat.beq Z0 ZM = true := by quickRfl

theorem zz_chk : Nat.beq (mulJ c rm Z0 Z0) one = true := by quickRfl

theorem j_chk : Nat.beq (cjP JP).1 Z0 = true := by quickRfl

theorem c_chk : Nat.beq (mP C1P JP).1 (mP JP C1P).1 = true := by quickRfl

theorem ca_chk : eqP (cjP C1P) GA = true := by quickRfl

theorem cb_chk : eqP (cjP H2) GB = true := by quickRfl

theorem cz_chk : eqP (cjP (V 5)) GZ = true := by quickRfl

end CertificateChecks.KernelJ4Gam

end
