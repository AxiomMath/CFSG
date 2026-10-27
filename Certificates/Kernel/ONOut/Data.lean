module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Orders.Cert3
public import Certificates.Data.Kernel.ONOut.Mat
public import Certificates.Data.GrSLitL34FactsCF23ONOutK2Data
public import CFSG.Certificates.Kernel.Orders.CertSplit

public section

namespace CFSG.KD.ONOut

@[expose] noncomputable def LO : Nat := Nat.sub (Nat.shiftLeft 1 23716) 1

@[expose] noncomputable def RM : Nat := Nat.sub (Nat.shiftLeft 1 154) 1

@[expose] noncomputable def CI : Nat := CFSG.KC.Ord.rep1 154 154

@[expose] noncomputable def CC : Nat := Nat.lor CI (Nat.shiftLeft CI 23716)

@[expose] noncomputable def ONE : Nat := CFSG.KC.Ord.rep1 155 154

@[expose] noncomputable def NEG : Nat := Nat.shiftLeft ONE 23716

@[expose] noncomputable def UP : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.sub (Nat.sub 154 i) 1)) 1)
      (Nat.succ (Nat.mul (Nat.succ 154) i)))) 154

@[expose] noncomputable def MUL : Nat → Nat → Nat := CFSG.KC.Ord.mul3s 154 23716 LO CI RM

@[expose] noncomputable def VLD : Nat → Bool := CFSG.KC.Ord.valid3 23716 LO

@[expose] def parF (t : Nat) : Nat := CFSG.ComponentClassification.SolMax.ONOut.spinPar[t]!

@[expose] def labF (t : Nat) : Nat := CFSG.ComponentClassification.SolMax.ONOut.spinLab[t]!

end CFSG.KD.ONOut

#kc_repo #kc_ktree CFSG.KD.ONOut MT "Certificates/Kernel/ONOut/data/mats.bin" 5929 4 47432 12357595460990684961

namespace CFSG.KD.ONOut

@[expose] noncomputable def WM : Nat :=
  CFSG.KC.ONOut.addM3 (nat_lit 23716) LO
    (CFSG.KC.ONOut.addM3 (nat_lit 23716) LO ONE (MUL (MT (nat_lit 0)) (MT (nat_lit 1))))
    (CFSG.KC.ONOut.negM3 (nat_lit 23716) LO
      (MUL (MUL (MT (nat_lit 0)) (MT (nat_lit 1))) (MT (nat_lit 1))))

end CFSG.KD.ONOut

#kc_repo #kc_ktree CFSG.KD.ONOut P1 "CFSG/Blueprint/Data/ONG1-f3r154B0.m1" 256 4 24045 9510399569759921264
#kc_repo #kc_ktree CFSG.KD.ONOut P2 "CFSG/Blueprint/Data/ONG1-f3r154B0.m2" 256 4 24045 4137249943231342429

set_option maxRecDepth 400000

#ks_chars CFSG.KD.ONOut.ONSA CFSG.Sporadic.ON.Native.seedA

#ks_chars CFSG.KD.ONOut.ONSB CFSG.Sporadic.ON.Native.seedB

#ks_chars CFSG.KD.ONOut.ONN0 CFSG.ComponentClassification.SolMax.ONOut.n0Code

#ks_chars CFSG.KD.ONOut.ONR CFSG.ComponentClassification.SolMax.ONOut.rCode

#ks_chars CFSG.KD.ONOut.ONV CFSG.ComponentClassification.SolMax.ONOut.vCode

#ks_chars CFSG.KD.ONOut.ONU CFSG.ComponentClassification.SolMax.ONOut.uCode

end
