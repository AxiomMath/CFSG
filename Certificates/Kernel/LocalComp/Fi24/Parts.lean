module

public import Certificates.Kernel.LocalComp.Fi24.Replay
public import Certificates.Data.Kernel.LocalComp.ElemParts
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CertificateChecks.KernelLC.F24

open CFSG.KC.LQT CFSG.KC.LocalComp.ElemParts
open CFSG.KD.LC.F24 (lay V P N)

@[expose] noncomputable def sqI (i : Nat) : Nat := Nat.land (TC i) 1048575

@[expose] noncomputable def cuI (i : Nat) : Nat := Nat.land (Nat.shiftRight (TC i) 20) 1048575

@[expose] noncomputable def ppI (i j : Nat) : Nat := TP (Nat.add (Nat.mul 4 i) j)

theorem kCube0 : cubeK lay V P N (TO 0) (sqI 0) (cuI 0) = true := by quickRfl
theorem kCube1 : cubeK lay V P N (TO 1) (sqI 1) (cuI 1) = true := by quickRfl
theorem kCube2 : cubeK lay V P N (TO 2) (sqI 2) (cuI 2) = true := by quickRfl
theorem kCube3 : cubeK lay V P N (TO 3) (sqI 3) (cuI 3) = true := by quickRfl

theorem kPair10 : pairK V P N (TO 1) (TO 0) (ppI 1 0) (ppI 0 1) = true := by quickRfl
theorem kPair20 : pairK V P N (TO 2) (TO 0) (ppI 2 0) (ppI 0 2) = true := by quickRfl
theorem kPair21 : pairK V P N (TO 2) (TO 1) (ppI 2 1) (ppI 1 2) = true := by quickRfl
theorem kPair30 : pairK V P N (TO 3) (TO 0) (ppI 3 0) (ppI 0 3) = true := by quickRfl
theorem kPair31 : pairK V P N (TO 3) (TO 1) (ppI 3 1) (ppI 1 3) = true := by quickRfl
theorem kPair32 : pairK V P N (TO 3) (TO 2) (ppI 3 2) (ppI 2 3) = true := by quickRfl

theorem kKer0 : kerK lay V TO (fun _ => 0) 4 0 10 = true := by quickRfl
theorem kKer1 : kerK lay V TO (fun _ => 0) 4 10 10 = true := by quickRfl
theorem kKer2 : kerK lay V TO (fun _ => 0) 4 20 10 = true := by quickRfl
theorem kKer3 : kerK lay V TO (fun _ => 0) 4 30 10 = true := by quickRfl
theorem kKer4 : kerK lay V TO (fun _ => 0) 4 40 10 = true := by quickRfl
theorem kKer5 : kerK lay V TO (fun _ => 0) 4 50 10 = true := by quickRfl
theorem kKer6 : kerK lay V TO (fun _ => 0) 4 60 10 = true := by quickRfl
theorem kKer7 : kerK lay V TO (fun _ => 0) 4 70 10 = true := by quickRfl

end CertificateChecks.KernelLC.F24
