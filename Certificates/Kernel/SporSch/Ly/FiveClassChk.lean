module

public import Certificates.Kernel.SporSch.Ly.FiveLanesData
public import Certificates.Kernel.SporSch.Ly.SevA
public import Certificates.Kernel.LyFive.Data
public import CFSG.RankThree.PartOne.KS.LyFiveInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.LyFiveSpec
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.LySeven
public import CFSG.Sporadic.Schreier.LySevenRep

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyFC

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy
open CertificateChecks.KernelSporSch.LyBS CertificateChecks.KernelSporSch.LySv
open CertificateChecks.KernelSporSch.LyFL CFSG.RankThree.PartOne.LyFive

@[expose] noncomputable def TW (w : List Int) : Nat := wordR 5 12 1332 111 8 L H CM RM GS GSI ONE w

@[expose] def invW (w : List Int) : List Int := w.reverse.map fun l => -l

@[expose] noncomputable def YY : Nat := mul (V 0) (V 1)

@[expose] noncomputable def nfE (c : Nat) (e : List Nat) : Nat := nfL (c % 5) fun j => e.getD j.val 0 % 5

theorem tx : Nat.beq (mul (TW xWord) (TW (invW xWord))) ONE = true := by quickRfl
theorem ty3 : Nat.beq (mul (TW y3Word) (TW (invW y3Word))) ONE = true := by quickRfl
theorem ty1 : Nat.beq (mul (TW y1Word) (TW (invW y1Word))) ONE = true := by quickRfl

theorem rx : rOK (mul (mul (TW (invW xWord)) D.XX) (TW xWord))
    ⟨CertificateChecks.KernelLyFive.D.RX⟩ = true := by quickRfl
theorem ry3 : rOK (mul (mul (TW (invW y3Word)) YY) (TW y3Word))
    ⟨CertificateChecks.KernelLyFive.D.RY3⟩ = true := by quickRfl
theorem ry1 : rOK (mul (mul (TW (invW y1Word)) YY) (TW y1Word))
    ⟨CertificateChecks.KernelLyFive.D.RY1⟩ = true := by quickRfl

theorem comm : (dLifts.all fun d => Nat.beq (mul (mul (wordL d.1) (nfE d.2.1 d.2.2)) YY)
      (mul YY (mul (wordL d.1) (nfE d.2.1 d.2.2)))) &&
    (uVecs.all fun u => Nat.beq (mul (nfE 0 u) YY) (mul YY (nfE 0 u))) = true := by quickRfl

end CertificateChecks.KernelSporSch.LyFC

end
