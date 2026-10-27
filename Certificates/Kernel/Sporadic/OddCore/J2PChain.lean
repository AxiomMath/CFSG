module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.J5B
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Sporadic.Schreier.PairJ2CheckInputs
meta import CFSG.Sporadic.Schreier.PairJ2CheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2PC

meta def sM : Array (Array Nat) := CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ()

@[expose] def noWords : List (List Int) := []

end CertificateChecks.KernelSpor.J2PC

#ks_rawchain CertificateChecks.KernelSpor.J2P 315 9 0 CertificateChecks.KernelSpor.J2PC.sM
  CFSG.Sporadic.Schreier.PairJ2.baseArr 7 CertificateChecks.KernelSpor.J2PC.noWords

namespace CertificateChecks.KernelSpor.J2PC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native

theorem bindsP : Binds 315 9 J2P.S 7 3 J2P.BP (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())
    CFSG.Sporadic.Schreier.PairJ2.baseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [
    CFSG.Sporadic.Schreier.PairNative.j2StrongArrs], fun j hj => ?_, by decide, by decide +kernel⟩
  have e : (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[j]! =
      hexTable 4 315 (315 * j) CFSG.Sporadic.Schreier.PairNative.j2StrongHex := by
    simp [CFSG.Sporadic.Schreier.PairNative.j2StrongArrs, hj,
      CFSG.Sporadic.Schreier.PairNative.j2Strong]
  rw [e, CertificateChecks.KernelMisc.J2F.JS.eq,
    CFSG.KC.Misc.HexFlat.hexTable_sound CertificateChecks.KernelMisc.J2F.JS.all j hj]
  have hs : Nat.beq (CertificateChecks.KernelMisc.J2F.JS.F j) (J2P.S j) = true := by
    interval_cases j <;> quickRfl
  rw [Nat.eq_of_beq_eq_true hs]

theorem permP : allN 7 (fun j => permOK 315 9 (mask 9) (315 * 9) (J2P.S j) (J2P.SI j)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.J2PC

end
