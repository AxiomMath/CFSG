module

public import Certificates.Data.Kernel.O8.SBCenL
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSTabData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.SBCenL CFSG.EvenSmallLie.OmegaEight.SpBranch

theorem sqBlk0 : sqBlk sActRow sMtRow 0 = true := by decide +kernel

theorem sqBlk1 : sqBlk sActRow sMtRow 1 = true := by decide +kernel

theorem sqBlk2 : sqBlk sActRow sMtRow 2 = true := by decide +kernel

theorem sqBlk3 : sqBlk sActRow sMtRow 3 = true := by decide +kernel

theorem sqBlk4 : sqBlk sActRow sMtRow 4 = true := by decide +kernel

theorem sqBlk5 : sqBlk sActRow sMtRow 5 = true := by decide +kernel

theorem sqBlk6 : sqBlk sActRow sMtRow 6 = true := by decide +kernel

theorem sqBlk7 : sqBlk sActRow sMtRow 7 = true := by decide +kernel

end CertificateChecks.KernelO8.SB3873

end
