module

public import CFSG.Certificates.Kernel.U6LinSound
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParDCert
import CFSG.Certificates.Kernel.U6LinProved

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6F2 CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (tBits aBits n0Bits n1Bits cMask hiMask dBlock dFb
  dCols dCheckW dEcols dQcols unpackBlk packBlks unpackN packN)

@[expose] noncomputable def dBlockK (v k : ℕ) : ℕ :=
  nIf(Nat.blt k 4,
    Nat.xor (mulF 8 (mulF 8 (packM 8 tBits) (fget v k 64)) (packM 8 tBits)) (fget v k 64),
    nIf(Nat.blt k 12,
      Nat.xor (Nat.xor (mulF 8 (mulF 8 (packM 8 (n0Bits ((k - 4) / 4))) (fget v ((k - 4) % 4) 64))
          (packM 8 (n1Bits ((k - 4) / 4))))
        (msumK 4 (cMask ((k - 4) / 4) ((k - 4) % 4)) fun m => fget v m 64))
        (msumK 4 (fget (fget v 4 64) (4 * ((k - 4) / 4) + (k - 4) % 4) 8)
          fun m => packM 8 (aBits m)),
      mulF 8 (fget v 4 64) (packM 8 hiMask)))

@[expose] noncomputable def dFbK (v : ℕ) : ℕ :=
  orN 13 fun k => Nat.shiftLeft (dBlockK v k) (Nat.mul k 64)

theorem dFb_eq (v : ℕ) : dFb v = dFbK v := by
  rw [dFb, packBlks_eq, packN_eq_proved]
  refine orN_congr fun k hk => ?_
  congr 1
  interval_cases k <;>
    simp only [dBlock, unpackBlk_eq, Nat.reduceLT, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceMul, Nat.reduceAdd, ite_true, ite_false, packM_bxor_proved, packM_bmul_proved,
      packM_unpackN_proved, packM_msum_proved, getD_unpackN_proved] <;> rfl

theorem dCheckW_true : dCheckW = true := by
  rw [dCheckW]
  refine certCheckWith_of_idRowsK_proved (F := (List.range (5 * 64)).map fun l => dFbK (2 ^ l))
    (B := dCols.toList) (fun l hl => by rw [getLD_map_range _ _ hl, dFb_eq]) rfl
    (by decide +kernel) (by decide +kernel) ?_
  decide +kernel

end CertificateChecks.KernelU6
