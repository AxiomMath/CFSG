module

public import Certificates.Kernel.Fi24Syl.Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi24Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbDefs

set_option maxRecDepth 100000

#kc_each CFSG.KD.Fi24Syl fi24sylChunk
  (fun c => CFSG.KC.Fi24Syl.chunkOK CFSG.KD.Fi24Syl.tops c (CFSG.KD.Fi24Syl.stK c)) 0 27

public section

namespace CFSG.KD.Fi24Syl

open CFSG.KC.Ord CFSG.KC.Fi24Syl CFSG.AGLEmbedding.R3.AlphaFi24

theorem fi24syl_final : concl (totK stK) = true := by quickRfl

theorem fi24syl_tops :
    topsOK tops (fi24Tidx.map fun i => (fi24Mod.acts.getD i default).mat) = true := by quickRfl

theorem fi24syl_consts : constsOK 3 6 42 7 3 L7 H7 CM7 RM ONE7 LV7 HV7 = true := by quickRfl

theorem fi24syl_neg_chunk : notB (chunkOK tops 7 (Nat.xor (stK 7) 1)) = true := by quickRfl

theorem fi24syl_neg_poison : notB (concl (Nat.add (totK stK) (Nat.shiftLeft 1 91854))) = true := by
  quickRfl

theorem fi24syl_neg_order : notB (concl (Nat.add (totK stK) (Nat.shiftLeft 6560 91812))) = true := by
  quickRfl

theorem fi24syl_neg_cnt : notB (concl (Nat.add (totK stK) (Nat.mul 2186 (rep1 42 30)))) = true := by
  quickRfl

theorem fi24syl_neg_cnt5 :
    notB (concl (Nat.add (totK stK) (Nat.mul 242 (Nat.shiftLeft (rep1 42 243) 21)))) = true := by
  quickRfl

theorem fi24syl_neg_tops :
    notB (topsOK (fun k => tops (Nat.add k 1))
      (fi24Tidx.map fun i => (fi24Mod.acts.getD i default).mat)) = true := by quickRfl

end CFSG.KD.Fi24Syl

end
