module

public import Certificates.Kernel.TitsN12.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsN12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.TitsN12K
open CertificateChecks.KernelSpor

theorem cU0 : canonK 1755 11 (mask 11) (1755 * 11) (U 0) = true := by quickRfl
theorem cU1 : canonK 1755 11 (mask 11) (1755 * 11) (U 1) = true := by quickRfl
theorem pU0 : permOK 1755 11 (mask 11) (1755 * 11) (U 0) (pinvS 1755 11 (mask 11) (U 0)) = true := by
  quickRfl
theorem pU1 : permOK 1755 11 (mask 11) (1755 * 11) (U 1) (pinvS 1755 11 (mask 11) (U 1)) = true := by
  quickRfl
theorem kU0 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK.LR TitsK.TRI TitsK.BP 5 0
    (U 0) = true := by quickRfl
theorem kU1 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK.LR TitsK.TRI TitsK.BP 5 0
    (U 1) = true := by quickRfl

@[expose] noncomputable def oneOK (R : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun r t _ => bAnd(memL r SH.C, List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) t)) R

theorem r3 : oneOK D.R1 = true := by quickRfl
theorem r5 : oneOK D.R2 = true := by quickRfl
theorem r9 : oneOK D.R4 = true := by quickRfl
theorem r17 : oneOK D.R8 = true := by quickRfl

@[expose] noncomputable def okW (u0 u1 c p j : Nat) : Bool :=
  bAnd(memL c SH.C, conjOK (fun j => Bool.rec (motive := fun _ => Nat) u1 u0 (Nat.beq j 0)) SH.C SH.L
    c p j)

@[expose] noncomputable def covL (a b : Nat) (W : List Nat) : Bool :=
  allL (fun c => bIf(in2 a b (gptC TitsH.LR TitsH.TR c 1), memL c W, true)) SF.C

@[expose] noncomputable def covW (a b : Nat) (E : List (Nat × Nat × Nat)) (R : List Nat) : Bool :=
  strictB (U 0) (fun u0 => strictB (U 1) (fun u1 => covL a b (walkK (okW u0 u1) E R)))

theorem cov3 : covW 3 4 D.E1 D.R1 = true := by quickRfl
theorem cov5 : covW 5 7 D.E2 D.R2 = true := by quickRfl
theorem cov9 : covW 9 13 D.E4 D.R4 = true := by quickRfl
theorem cov17 : covW 17 25 D.E8 D.R8 = true := by quickRfl

end CertificateChecks.KernelTitsN12

end
