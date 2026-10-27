
module

public import CFSG.Certificates.Kernel.GH74Tab.SearchSound
public import Certificates.Kernel.GH74Tab.Search
public import Certificates.Kernel.GH74Tab.Trans6
public import Certificates.Kernel.GH74Tab.Trans7
public import Certificates.Kernel.GH74Tab.WB7

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab CFSG.GH74.GLS.C3.Layer2.Model

theorem c5042_claim6 : (mkTab 6).claimG (admP dat.adm) = true :=
  claimG_adm c5042_trans6 c5042_data c5042_search

theorem c5042_claim7 : (mkTab 7).claimG (admP dat.adm) = true :=
  claimG_adm c5042_trans7 c5042_data c5042_search

theorem c5042_claim7w : (mkTab 7).claimG (admP dat.adm7) = true :=
  claimG_adm7 c5042_trans7 c5042_data c5042_search c5042_wb7

end CFSG.KD.GH74Tab

end
