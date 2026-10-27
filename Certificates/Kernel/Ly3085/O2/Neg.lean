module

public import Certificates.Kernel.Ly3085.O2.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.LyO2

open CFSG.KC.LyOm CFSG.KC.Ord

theorem consts : constsOK C = true := by quickRfl

theorem neg_gen : notB (treeLeaf C KX PT P1 P0 n 1) = true := by quickRfl

theorem neg_keys : notB (treeLeaf C PT PT P0 P1 n 1) = true := by quickRfl

theorem neg_sort : notB (sortChunk KX PT n 0 64) = true := by quickRfl

theorem neg_count : notB (sortChunk KX SG 1000 0 64) = true := by quickRfl

theorem neg_mask : notB (constsOK { C with MS := 0 :: MS.tail }) = true := by quickRfl

end CFSG.KD.LyO2
