module

public import Certificates.Kernel.SporSch.Mathieu.M12Data
public import Certificates.Data.Kernel.KGC31PB
public import CFSG.Quasithin.Vol2.KGFactC31M12Data

public section

namespace CertificateChecks.KernelKGC31M12

open CFSG.KC.Enum CFSG.KC.KGC31P CertificateChecks.KernelSporSch

@[expose] noncomputable def G (l : Int) : Nat := if l = 1 then M12Q.S 0 else M12Q.S 1

@[expose] noncomputable def pw (wd : List Int) : Nat := pword 12 4 G wd

@[expose] noncomputable def X5 : Nat := pw CFSG.Quasithin.KGC31.M12.w5
@[expose] noncomputable def X11 : Nat := pw CFSG.Quasithin.KGC31.M12.w11

@[expose] noncomputable def TL : List (List Nat) := trPL 12 4 M12Q.LR M12Q.TR 5

@[expose] noncomputable def I : List Nat := pfilterProducts 12 4 (pord 12 4 2) TL (pidn 12 4) []

@[expose] noncomputable def actAll (m x : Nat) : Bool :=
  (List.range m).all fun a => I.all (pactOne 12 4 m (ppw 12 4 x a))

end CertificateChecks.KernelKGC31M12

end
