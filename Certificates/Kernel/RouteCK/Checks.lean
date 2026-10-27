module

public import Certificates.Data.Kernel.RouteCK
public import Certificates.Data.RouteCWit
import all Certificates.Data.RouteCWit

public section

namespace Certificates.Kernel.RouteCK

open CFSG.CGT.PushingUpLit.CGT6.RouteC CFSG.CGT.PushingUpLit.CGT6.RouteCK

theorem chRC6 : checkK (survivors 6) 6 wit6 = true := by decide +kernel

theorem chRC5 : checkK (survivors 5) 5 wit5 = true := by decide +kernel

theorem chRC4 : checkK (survivors 4) 4 wit4 = true := by decide +kernel

end Certificates.Kernel.RouteCK
