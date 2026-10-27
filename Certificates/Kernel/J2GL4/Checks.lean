module

public import Certificates.Kernel.J2GL4.Data
public import CFSG.Sporadic.Bridge.J2Native
public import CFSG.RankThree.PartTwo.Sec17.J2NotGL4Words

public section

namespace CFSG.KD.J2GL4

open CFSG.Sporadic.Bridge.J2 CFSG.RankThree.PartTwo.Sec17.J2NotGL4

theorem ch40520_wx7 : (lwordL natX natXi wx7 idL == mX7) = true := by decide +kernel

theorem ch40520_wy7 : (lwordL natX natXi wy7 idL == mY7) = true := by decide +kernel

theorem ch40520_wa5 : (lwordL natX natXi wa5 idL == mA5) = true := by decide +kernel

theorem ch40520_wb5 : (lwordL natX natXi wb5 idL == mB5) = true := by decide +kernel

theorem ch40520_wy5 : (lwordL natX natXi wy5 idL == mY5) = true := by decide +kernel

end CFSG.KD.J2GL4

end
