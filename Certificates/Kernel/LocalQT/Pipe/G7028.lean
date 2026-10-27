module

public import Certificates.Kernel.LocalQT.Pipe.C7028
public import CFSG.Certificates.Kernel.LocalQTPipeMasks
import Certificates.Kernel.LocalQT.Pipe.C4050a
import Certificates.Kernel.LocalQT.Pipe.C4050s
import Certificates.Kernel.LocalQT.Pipe.C4050m
import Certificates.Kernel.LocalQT.Pipe.C4050r
import Certificates.Kernel.LocalQT.Pipe.C4050b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2CheckInputs

set_option maxRecDepth 100000

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.LQT.S CFSG.KC.LQT.PP CFSG.KD.LQT.C4050

theorem j2_masks : ∀ h < j2Data.xs.size,
    (∀ i < 4725, (j2Blocks.getD h #[]).getD i false = true ↔ (getK BM h).testBit i = true) ∧
      ∀ i, 4725 ≤ i → (getK BM h).testBit i = false :=
  CFSG.KC.LQT.PPC.masks_sound (N := 4725) (W := 13) (by decide) (by decide) AaC AbC parC genC repC
    j2Data.prog j2Data.qp j2Data.xs TF MF SL ML REPS OML BM BWL PRK GNK RPK RIK QPK QGK DPK 170
    224 5 945 6 hPa hPb h0 h1 hT hpt hgt hrt hPK hGK hRK hso hsn hq rfl S.all hid hM rfl M.all hXM
    hrs (by decide) R.all rfl B.all

theorem j2_block_sizes :
    (List.range j2Data.xs.size).all (fun h => blkSize 4725 (j2Blocks.getD h #[]) == 1 ||
      blkSize 4725 (j2Blocks.getD h #[]) % 3 == 0) = true := by
  have hsz : j2Data.xs.size = 6 := rfl
  rw [List.all_eq_true]
  intro h hh
  rw [List.mem_range] at hh
  rw [CFSG.KC.LQT.PPC.blkSize_popK (j2_masks h hh).1]
  have hc := List.all_eq_true.1 ch7028 h (List.mem_range.2 (by rw [← hsz]; exact hh))
  exact hc

end CFSG.QuasithinUnique.Setup.X1

end
