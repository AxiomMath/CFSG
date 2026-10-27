module

public import Certificates.Data.Kernel.E6Syl3C
public import Certificates.Kernel.E6Syl3.Data
public import Certificates.Kernel.E6Syl3.DataP
public import Certificates.Kernel.E6Syl3.DataC

public section

namespace CFSG.KD.E6Syl3

open CFSG.KC.E6Syl3

theorem ch214106_gen : genN3 gw = true := by decide +kernel

theorem ch214106_elems : caseIElems qt kw = true := by decide +kernel

theorem ch214106_pairs : caseIPairs qt kw lt wd o3 cw = true := by decide +kernel

end CFSG.KD.E6Syl3
