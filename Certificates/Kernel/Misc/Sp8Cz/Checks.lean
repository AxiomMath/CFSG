module

public import Certificates.Data.Kernel.Misc.Sp8Cz
public import Certificates.Kernel.Misc.Sp8Cz.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp8Cz

theorem cz5_tab_ok : czTabK REC 12960 = true := by quickRfl

theorem cz5_e9tab_ok : e9TabK REC 12969 0 1 9 = true ∧ e9TabK REC 12979 3 7 9 = true ∧
    e9TabK REC 12989 0 7 9 = true := ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem cz5_e9mem_ok : e9MemK REC 12969 0 1 = true ∧ e9MemK REC 12979 3 7 = true ∧
    e9MemK REC 12989 0 7 = true := ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem cz5_cntW : cntW = 18 := by decide +kernel

theorem cz5_cntW' : cntW' = 720 := by decide +kernel

end CFSG.KD.Sp8Cz

end
