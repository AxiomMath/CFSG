module

public import Certificates.Data.Kernel.E6Syl3P
public import Certificates.Kernel.E6Syl3.Data
public import Certificates.Kernel.E6Syl3.DataP

public section

namespace CFSG.KD.E6Syl3

open CFSG.KC.E6Syl3

theorem ch214107_wd : wdOK gw qt wd = true := by decide +kernel

theorem ch214107_lt : ltOK gw qt lt = true := by decide +kernel

theorem ch214107_o3 : o3OK lt wd o3 = true := by decide +kernel

theorem ch214107_pairs : pairsCheck qt kw lt wd o3 bw = true := by decide +kernel

end CFSG.KD.E6Syl3
