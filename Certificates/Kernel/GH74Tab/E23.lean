module

public import Certificates.Kernel.GH74Tab.Data
public import Certificates.Kernel.GH74Tab.DataE23
public import Certificates.Data.Kernel.GH74Tab.E23

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab CFSG.GH74.GLS.C3.Layer2.Model

theorem c5043_e2 : e2OK dat dat.adm E23.w2 E23.w3 = true := by decide +kernel

theorem c5044_e3 : e3OK dat dat.adm7 E23.w4 E23.wa E23.wc = true := by decide +kernel

theorem c5044_wAct : (mkTab 7).wActOKE3 = true := by decide +kernel

end CFSG.KD.GH74Tab

end
