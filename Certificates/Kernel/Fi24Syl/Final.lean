module

public import CFSG.Certificates.Kernel.Fi24Syl.Sound
import Certificates.Kernel.Fi24Syl.Checks

public section

namespace CFSG.KD.Fi24Syl

open CFSG.KC.Fi24Syl CFSG.KS.Fi24Syl

private theorem fi24syl_chunks : ∀ c < 27, chunkOK tops c (stK c) = true := by
  intro c hc
  interval_cases c
  exacts [fi24sylChunk0, fi24sylChunk1, fi24sylChunk2, fi24sylChunk3, fi24sylChunk4,
    fi24sylChunk5, fi24sylChunk6, fi24sylChunk7, fi24sylChunk8, fi24sylChunk9, fi24sylChunk10,
    fi24sylChunk11, fi24sylChunk12, fi24sylChunk13, fi24sylChunk14, fi24sylChunk15,
    fi24sylChunk16, fi24sylChunk17, fi24sylChunk18, fi24sylChunk19, fi24sylChunk20,
    fi24sylChunk21, fi24sylChunk22, fi24sylChunk23, fi24sylChunk24, fi24sylChunk25,
    fi24sylChunk26]

theorem fi24syl_facts : CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi24Facts
    CFSG.HardMathSupport.Timmesfeld.SporadicRank.fi24Matrices := by
  have hT : topsOK tops tops9 = true := by
    rw [tops9_eq]
    exact fi24syl_tops
  exact fi24Facts_of_kc hT fi24syl_chunks fi24syl_final

end CFSG.KD.Fi24Syl

end
