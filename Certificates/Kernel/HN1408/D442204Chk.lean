module

public import Certificates.Kernel.HN1408.D442204Defs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.D442204Syl
public import Certificates.Kernel.HN1408.Y442202Inst

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch442204cov sl CFSG.KD.HN1408.D442204.covS 0 20

public section

namespace CFSG.KD.HN1408.D442204

open CFSG.KC.Enum CFSG.EvenSporadicStandard.HNRecog.Simple2S5 CFSG.KD.HN1408.Y442202

theorem head_ok : headK H = true := by quickRfl

theorem kill_ok : allN 16 (killK killData) = true := by quickRfl

theorem fix_ok : fixK fixPt = true := by quickRfl

theorem syl7_gens : sylGK S7.G 0 1 = true := by quickRfl

theorem syl9_gens : sylGK S9.G 1 2 = true := by quickRfl

theorem syl125_gens : sylGK S125.G 2 2 = true := by quickRfl

theorem syl7_rec : recOK S7.G S7.GI S7.k S7.cnt S7.T S7.PL S7.POS S7.SRT S7.SRI = true := by
  quickRfl

theorem syl9_rec : recOK S9.G S9.GI S9.k S9.cnt S9.T S9.PL S9.POS S9.SRT S9.SRI = true := by
  quickRfl

theorem syl125_rec :
    recOK S125.G S125.GI S125.k S125.cnt S125.T S125.PL S125.POS S125.SRT S125.SRI = true := by
  quickRfl

theorem syl_cnt : S7.cnt = 7 ∧ S9.cnt = 9 ∧ S125.cnt = 125 ∧ S7.k = 1 ∧ S9.k = 2 ∧ S125.k = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end CFSG.KD.HN1408.D442204

end
