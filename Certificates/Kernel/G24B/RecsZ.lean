module

public import Certificates.Kernel.G24B.Recs
import CFSG.Certificates.Kernel.Common.F2Bfs

public section

set_option maxRecDepth 100000

namespace CFSG.KD.G24B

open CFSG.Quasithin.St84.G24Ident

@[expose] def wZ1 : List (List (Fin 6 × Bool)) := [pc1.getD 8 [], pc1.getD 9 []]

@[expose] def wZ2 : List (List (Fin 6 × Bool)) :=
  [pc2.getD 6 [], pc2.getD 7 [], pc2.getD 8 [], pc2.getD 9 []]

@[expose] noncomputable def GZ1 : List Nat := wZ1.map blowW
@[expose] noncomputable def GZ2 : List Nat := wZ2.map blowW

end CFSG.KD.G24B

#kc_f2bfs CFSG.KD.G24B.EZ1 28 CFSG.KD.G24B.GZ1 4096 6 12
#kc_f2bfs CFSG.KD.G24B.EZ2 28 CFSG.KD.G24B.GZ2 4096 6 12

end
