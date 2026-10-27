module

public import Certificates.Data.Kernel.G2Three.Sec1T1
public import Certificates.Kernel.G2Three.Sec1T1Rec
public import Certificates.Kernel.G2Three.Sec1T1Rec2
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three

theorem r1_B : (Nat.beq (R1B 0) ONEP && parK R1BPA R1BPB R1BPOS 4 31 1 &&
    closP R1B (fun s => R1U (R1BG s)) R1BPOS 32 4 0 128 2 && sortK R1B R1BSRT R1BSRI 32 1) =
    true := by quickRfl

theorem r1_conjS : (ltK R1SC 576 4 1 && ltK R1SD 576 6 1 && ltK R1SW 5 6 1 &&
    eqK (fun q => R1H (R1SC (R1P4J q))) (fun q => R1H (R1SD q)) (fun q => R1H (R1SC (R1P4I q)))
      (fun _ => R1U 7) 6 1) = true := by quickRfl

theorem r1_conjSW : neK (fun q => R1H (R1SD (Nat.div q 64)))
    (fun q => R1U (R1SG (R1SW (Nat.div q 64)))) (fun q => R1S (Nat.mod q 64))
    (fun q => R1H (R1SD (Nat.div q 64))) 384 6 = true := by quickRfl

theorem r1_conjB : (ltK R1BC 576 4 1 && ltK R1BD 576 6 1 && ltK R1BW 4 6 1 &&
    eqK (fun q => R1H (R1BC (R1P4J q))) (fun q => R1H (R1BD q)) (fun q => R1H (R1BC (R1P4I q)))
      (fun _ => R1U 7) 6 1) = true := by quickRfl

theorem r1_conjBW : neK (fun q => R1H (R1BD (Nat.div q 32)))
    (fun q => R1U (R1BG (R1BW (Nat.div q 32)))) (fun q => R1B (Nat.mod q 32))
    (fun q => R1H (R1BD (Nat.div q 32))) 192 3 = true := by quickRfl

end CFSG.KD.G2Three.Sec1

end
