
module

public import Certificates.Kernel.Sporadic.Fi22.F1OuterT
public import Certificates.Kernel.Sporadic.Fi22.F1OuterS
public import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.SporSch.Derivs
public import CFSG.Monster.B.Fischer.Fi22OuterData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22F1O

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KS.SporSch
open CFSG.Monster.B.Fischer CertificateChecks.KernelSpor

@[expose] noncomputable def codesK (cs : List Char) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun ch _ ih => bAnd(Nat.blt (Char.toNat ch) (nat_lit 52), ih)) cs

@[expose] noncomputable def permSl (s : Nat) : Bool :=
  allN 20 (fun j => strictB (Nat.add (Nat.mul 20 s) j) (fun L => bIf(Nat.blt L 151,
    permB 3510 12 (Fi22OutT.L L), true)))

end CertificateChecks.KernelSpor.Fi22F1O

#kon_slices CertificateChecks.KernelSpor.Fi22F1O.permSl 0 8

#kon_join CertificateChecks.KernelSpor.Fi22F1O.permAll CertificateChecks.KernelSpor.Fi22F1O.permSl 8

namespace CertificateChecks.KernelSpor.Fi22F1O

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KS.SporSch
open CFSG.Monster.B.Fischer CertificateChecks.KernelSpor

theorem perm693 : allN 104 (fun L => permB 693 10 (Fi22O693T.L L)) = true := by quickRfl
theorem perm256 : allN 16 (fun L => permB 256 9 (Fi22O256T.L L)) = true := by quickRfl

theorem mLt : allN 693 (fun i => Nat.blt (pg 12 (mask 12) (Fi22OMP.F 0) i) 3510) = true := by
  quickRfl
theorem tLt : allN 256 (fun i => Nat.blt (pg 12 (mask 12) (Fi22OTP.F 0) i) 3510) = true := by
  quickRfl
theorem wLt : allN 693 (fun i => Nat.blt (pg 12 (mask 12) (Fi22OWO.F 0) i) 693) = true := by
  quickRfl

theorem codesU : codesK Fi22OUP.chars = true := by quickRfl
theorem codesV : codesK Fi22OTV.chars = true := by quickRfl
theorem lenU : Fi22OUP.chars.length = 693 * 6 := by decide +kernel
theorem lenV : Fi22OTV.chars.length = 46 * 6 := by decide +kernel

theorem dM : derivK fi22OuterMGenCount 17 fi22OuterMDerivations = true := by quickRfl
theorem dT : derivK fi22OuterTGenCount 13 fi22OuterTDerivations = true := by quickRfl
theorem dT256 : derivK fi22OuterT256GenCount 16 fi22OuterT256Derivations = true := by quickRfl
theorem dU : derivK fi22OuterUnitaryGenCount 49 fi22OuterUnitaryDerivations = true := by quickRfl
theorem dM693 : derivK fi22OuterM693GenCount 15 fi22OuterM693Derivations = true := by quickRfl
theorem dMC : derivK fi22OuterMComm693GenCount 14 fi22OuterMComm693Derivations = true := by
  quickRfl
theorem dD : derivK fi22OuterD693GenCount 11 fi22OuterD693Derivations = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22F1O

end
