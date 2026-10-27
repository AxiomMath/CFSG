module

public import Certificates.Kernel.K133.GBarDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelK133

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin

@[expose] noncomputable def GB.SK : List Nat := (List.range 14400).map GB.SKT

theorem gbKeys : keysSK 256 9 [4, 1, 8, 16] GB.N GB.T GB.SK = true := by quickRfl

theorem gbN : Nat.beq GB.N 14400 = true := by quickRfl

theorem gbPerm : allN 11
    (fun k => permOK 256 9 (mask 9) (256 * 9) (GB.G k) (pinvS 256 9 (mask 9) (GB.G k))) = true := by
  quickRfl

theorem cov0 : allBlk 0 coverK 4800 = true := by quickRfl
theorem cov1 : allBlk 4800 coverK 4800 = true := by quickRfl
theorem cov2 : allBlk 9600 coverK 4800 = true := by quickRfl

theorem pows : allN 624 powK = true := by quickRfl

theorem ua0 : allBlk 0 pairA 25 = true := by quickRfl
theorem ua1 : allBlk 25 pairA 25 = true := by quickRfl
theorem ua2 : allBlk 50 pairA 25 = true := by quickRfl
theorem ua3 : allBlk 75 pairA 25 = true := by quickRfl
theorem ua4 : allBlk 100 pairA 25 = true := by quickRfl
theorem ua5 : allBlk 125 pairA 25 = true := by quickRfl
theorem ua6 : allBlk 150 pairA 25 = true := by quickRfl
theorem ua7 : allBlk 175 pairA 25 = true := by quickRfl
theorem ua8 : allBlk 200 pairA 25 = true := by quickRfl
theorem ua9 : allBlk 225 pairA 25 = true := by quickRfl
theorem ua10 : allBlk 250 pairA 25 = true := by quickRfl
theorem ua11 : allBlk 275 pairA 25 = true := by quickRfl
theorem ua12 : allBlk 300 pairA 25 = true := by quickRfl
theorem ua13 : allBlk 325 pairA 25 = true := by quickRfl
theorem ua14 : allBlk 350 pairA 25 = true := by quickRfl
theorem ua15 : allBlk 375 pairA 25 = true := by quickRfl
theorem ua16 : allBlk 400 pairA 25 = true := by quickRfl
theorem ua17 : allBlk 425 pairA 25 = true := by quickRfl
theorem ua18 : allBlk 450 pairA 25 = true := by quickRfl

theorem pb0 : allBlk 0 pairB 48 = true := by quickRfl
theorem pb1 : allBlk 48 pairB 48 = true := by quickRfl
theorem pb2 : allBlk 96 pairB 48 = true := by quickRfl
theorem pb3 : allBlk 144 pairB 48 = true := by quickRfl
theorem pb4 : allBlk 192 pairB 48 = true := by quickRfl
theorem pb5 : allBlk 240 pairB 48 = true := by quickRfl
theorem pb6 : allBlk 288 pairB 48 = true := by quickRfl
theorem pb7 : allBlk 336 pairB 48 = true := by quickRfl
theorem pb8 : allBlk 384 pairB 48 = true := by quickRfl
theorem pb9 : allBlk 432 pairB 48 = true := by quickRfl
theorem pb10 : allBlk 480 pairB 48 = true := by quickRfl
theorem pb11 : allBlk 528 pairB 48 = true := by quickRfl
theorem pb12 : allBlk 576 pairB 48 = true := by quickRfl

end CertificateChecks.KernelK133

end
