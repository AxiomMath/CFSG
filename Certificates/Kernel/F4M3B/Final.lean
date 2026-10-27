module

public import Certificates.Kernel.F4M3B.Checks
public import CFSG.Certificates.Kernel.F4M3BSound

public section

namespace CFSG.KC.F4M3B

open CFSG.Quasithin.H13.L34

theorem all_check : M3.all.all M3.check = true :=
  List.all_eq_true.2 fun A _ => check_of_chkN ch7052 A

end CFSG.KC.F4M3B

end
