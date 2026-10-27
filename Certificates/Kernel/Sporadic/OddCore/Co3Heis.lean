module

public import Certificates.Kernel.Sporadic.OddCore.Co3Fus
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co3Check
meta import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co3Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#ks_chars CertificateChecks.KernelSpor.Co3HT
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.co3HeisHex
#kmisc_hexflat CertificateChecks.KernelSpor.Co3HT
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.co3HeisHex 3 276 9 4

namespace CertificateChecks.KernelSpor.Co3Fus

open CFSG.Sporadic.SmallOddCore.Native CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

meta def hiM : Array (Array Nat) := (List.range 4).toArray.map fun k =>
  CFSG.Monster.B.Co2.Native.invCand 276 (natArr (co3HeisTbl k))

end CertificateChecks.KernelSpor.Co3Fus

#kmisc_packarrs CertificateChecks.KernelSpor.Co3HI CertificateChecks.KernelSpor.Co3Fus.hiM 9

namespace CertificateChecks.KernelSpor.Co3Fus

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def pw (X : Nat) : Nat → Nat
  | 0 => idK
  | e + 1 => pc X (pw X e)

@[expose] noncomputable def hW (c : Nat) : Nat :=
  pc (pc (pc (Co3HI (2 * c)) (Co3HI (2 * c + 1))) (Co3HT.F (2 * c))) (Co3HT.F (2 * c + 1))

@[expose] noncomputable def hTau (c : Nat) : Nat := nIf(Nat.beq c 0, Co3Z, Co3Tt)

@[expose] noncomputable def hTabK (k : Nat) : Bool :=
  bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3HT.F k),
  bAnd(invEqK 276 9 (mask 9) (276 * 9) (Co3HT.F k) (Co3HI k),
  bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3HI k),
  bAnd(Co3Text.hiOK (Co3HT.F k), bAnd(Co3C.sift (Co3HT.F k),
    Nat.beq (pw (Co3HT.F k) 5) idK)))))

@[expose] noncomputable def heisK (c : Nat) : Bool :=
  bAnd(hTabK (2 * c), bAnd(hTabK (2 * c + 1), bAnd(Nat.beq (pw (hW c) 5) idK,
  bAnd(bIf(Nat.beq (hW c) idK, false, true),
  bAnd(Nat.beq (pc (Co3HT.F (2 * c)) (hW c)) (pc (hW c) (Co3HT.F (2 * c))),
  bAnd(Nat.beq (pc (Co3HT.F (2 * c + 1)) (hW c)) (pc (hW c) (Co3HT.F (2 * c + 1))),
    Nat.beq (pc (pc (hTau c) (Co3HT.F (2 * c))) (hTau c)) (Co3HI (2 * c))))))))

theorem heis_ok : bAnd(heisK 0, heisK 1) = true := by
  quickRfl

theorem heis_neg : Nat.beq (pc (pc Co3Tt (Co3HT.F 0)) Co3Tt) (Co3HI 0) = false ∧
    Nat.beq (pc (Co3HT.F 0) (Co3HT.F 1)) (pc (Co3HT.F 1) (Co3HT.F 0)) = false := by
  decide +kernel

@[expose] noncomputable def aEntK (i : Nat) : Bool :=
  bAnd(involK (Co3E.T i), Nat.beq (fl (r32 Co3WJ i)) 1)

@[expose] noncomputable def aIdx : List Nat := (List.range 1024).filter aEntK

@[expose] noncomputable def commK (i j : Nat) : Bool :=
  Nat.beq (pc (Co3E.T i) (Co3E.T j)) (pc (Co3E.T j) (Co3E.T i))

@[expose] noncomputable def rankK (b : Nat) : Bool :=
  decide ((aIdx.countP fun i => decide (b ≤ aIdx.countP fun j => commK i j)) ≤ 30)

theorem rank_ok : rankK 31 = true := by
  quickRfl

theorem rank_neg : rankK 1 = false := by
  decide +kernel

end CertificateChecks.KernelSpor.Co3Fus

end
