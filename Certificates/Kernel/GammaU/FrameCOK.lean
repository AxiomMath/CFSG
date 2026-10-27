module

public import Certificates.Kernel.GammaU.Frame0Data
public import Certificates.Kernel.GammaU.Frame1Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.GUFC0 cf16982acv CFSG.KD.GUFC0.cv 0 6
#kc_each CFSG.KD.GUFC0 cf16982afr CFSG.KD.GUFC0.fr 0 6
#kc_each CFSG.KD.GUFC1 cf16982bcv CFSG.KD.GUFC1.cv 0 5
#kc_each CFSG.KD.GUFC1 cf16982bfr CFSG.KD.GUFC1.fr 0 5

namespace CFSG.KD.GUFC0

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.KC.GUF

#kc_forall_chunks cf16982a_cvall (fun p => cv p = true) 6 CFSG.KD.GUFC0.cf16982acv 1

#kc_forall_chunks cf16982a_frall (fun p => fr p = true) 6 CFSG.KD.GUFC0.cf16982afr 1

theorem cf16982a_n2 : n2OK CFSG.KD.GUC0.TH CFSG.KD.GUT0.N2 NA CFSG.KD.GUT0.NN = true := by
  quickRfl

theorem cf16982a_pg : pgOK CFSG.KD.GUC0.TH PG = true := by quickRfl

theorem cf16982a_lt : ltOK CFSG.KD.GUCC.TB 0 LT = true := by quickRfl

theorem cf16982a_tree : treeOK NA CFSG.KD.GUT0.NN CFSG.KD.GUO.SM PG TR = true := by quickRfl

theorem cf16982a_lists : lists = true := by quickRfl

theorem cf16982_pc : pcOK CFSG.KD.GUCC.TB PT CM = true := by quickRfl

end CFSG.KD.GUFC0

namespace CFSG.KD.GUFC1

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.KC.GUF

#kc_forall_chunks cf16982b_cvall (fun p => cv p = true) 5 CFSG.KD.GUFC1.cf16982bcv 1

#kc_forall_chunks cf16982b_frall (fun p => fr p = true) 5 CFSG.KD.GUFC1.cf16982bfr 1

theorem cf16982b_n2 : n2OK CFSG.KD.GUC0.TH CFSG.KD.GUT1.N2 NA CFSG.KD.GUT1.NN = true := by
  quickRfl

theorem cf16982b_pg : pgOK CFSG.KD.GUC0.TH PG = true := by quickRfl

theorem cf16982b_lt : ltOK CFSG.KD.GUCC.TB 1 LT = true := by quickRfl

theorem cf16982b_tree : treeOK NA CFSG.KD.GUT1.NN CFSG.KD.GUO.SM PG TR = true := by quickRfl

theorem cf16982b_lists : lists = true := by quickRfl

end CFSG.KD.GUFC1

end
