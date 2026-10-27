module

public import Certificates.Kernel.HS100.KDData
public import Certificates.Data.Kernel.LocalComp.ExcDeriv
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.LocalComp.ExcDeriv
open CFSG.LocalAnalysis.GLTheoremA.KD264HS

theorem KD.perm : (permOK 100 7 (mask 7) (100 * 7) (HP.F 0) (HPI 0) &&
    permOK 100 7 (mask 7) (100 * 7) (HP.F 1) (HPI 1)) = true := by quickRfl

theorem KD.sift : (allN 2 fun j => Nat.beq (Nat.shiftRight (HP.F j) (100 * 7)) 0 &&
    allN 100 (fun t => Nat.blt (pg 7 (mask 7) (HP.F j) t) 100) &&
    siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HC.LR HC.TRI HC.BP 5 0 (HP.F j)) = true := by
  quickRfl

theorem KD.N : Nat.beq KD3.N 123200 = true := by quickRfl

theorem KD.CS : KD3.CS = [123200] := by decide +kernel

theorem KD.OFF : KD3.OFF = [0] := by decide +kernel

theorem KD.off : offOK KD3.CS KD3.OFF KD3.N = true := by quickRfl

theorem KD.gp : (Nat.beq (KD3.GP 0) (HP.F 0) && Nat.beq (KD3.GP 1) (HP.F 1) &&
    permOK 100 7 (mask 7) (100 * 7) (HP.F 0) (KD3.GIP 0) &&
    permOK 100 7 (mask 7) (100 * 7) (HP.F 1) (KD3.GIP 1) &&
    canonK 100 7 (mask 7) (100 * 7) (KD3.GP 0) && canonK 100 7 (mask 7) (100 * 7) (KD3.GIP 0) &&
    canonK 100 7 (mask 7) (100 * 7) (KD3.GP 1) && canonK 100 7 (mask 7) (100 * 7) (KD3.GIP 1)) =
    true := by quickRfl

theorem KD.letters : (lettersK 2 zW && lettersK 2 m1W && lettersK 2 m2W && lettersK 2 m3W) = true := by
  quickRfl

theorem KD.z : (Nat.beq (KD3.E 0) (kdW zW) &&
    Nat.beq (kp (kp (kdW zW) (kdW zW)) (kdW zW)) (pidn 100 7) &&
    neCK 100 7 (mask 7) (100 * 7) (kdW zW) (pidn 100 7)) = true := by quickRfl

theorem KD.moore : (Nat.beq (kp (kp (kdW m1W) (kdW m1W)) (kdW m1W)) (pidn 100 7) &&
    Nat.beq (kp (kdW m2W) (kdW m2W)) (pidn 100 7) &&
    Nat.beq (kp (kdW m3W) (kdW m3W)) (pidn 100 7) &&
    Nat.beq (kp (kp (kp (kdW m1W) (kdW m2W)) (kp (kdW m1W) (kdW m2W))) (kp (kdW m1W) (kdW m2W)))
      (pidn 100 7) &&
    Nat.beq (kp (kp (kp (kdW m2W) (kdW m3W)) (kp (kdW m2W) (kdW m3W))) (kp (kdW m2W) (kdW m3W)))
      (pidn 100 7) &&
    Nat.beq (kp (kp (kdW m1W) (kdW m3W)) (kp (kdW m1W) (kdW m3W))) (pidn 100 7) &&
    neCK 100 7 (mask 7) (100 * 7) (kdW m1W) (pidn 100 7) &&
    Nat.beq (kp (kdW m1W) (kdW zW)) (kp (kdW zW) (kdW m1W)) &&
    Nat.beq (kp (kdW m2W) (kdW zW)) (kp (kdW zW) (kdW m2W)) &&
    Nat.beq (kp (kdW m3W) (kdW zW)) (kp (kdW zW) (kdW m3W))) = true := by quickRfl

end CertificateChecks.KernelHS100

end
