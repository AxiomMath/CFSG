
module

public import Certificates.Data.Kernel.Q9Lg

public section

namespace CFSG.KC.Q9Lg

open CFSG.KC.Q9SL2

theorem chkHistIK_true : chkHistIK = true := by decide +kernel

theorem chkHistOK_true : chkHistOK = true := by decide +kernel

end CFSG.KC.Q9Lg
