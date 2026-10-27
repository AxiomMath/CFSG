module

public import Certificates.Kernel.SporSch.Mathieu.M11Data
public import Certificates.Data.Kernel.KGC31PB
public import CFSG.Quasithin.Vol2.KGFactC31M11Data

public section

namespace CertificateChecks.KernelKGC31M11

open CFSG.KC.Enum CFSG.KC.KGC31P CertificateChecks.KernelSporSch

@[expose] noncomputable def G (l : Int) : Nat := if l = 1 then M11Q.S 0 else M11Q.S 1

@[expose] noncomputable def pw (wd : List Int) : Nat := pword 11 4 G wd

@[expose] noncomputable def X5 : Nat := pw CFSG.Quasithin.KGC31.M11.w5
@[expose] noncomputable def X11 : Nat := pw CFSG.Quasithin.KGC31.M11.w11

@[expose] noncomputable def TL : List (List Nat) := trPL 11 4 M11Q.LR M11Q.TR 4

@[expose] noncomputable def I : List Nat := pfilterProducts 11 4 (pord 11 4 2) TL (pidn 11 4) []

@[expose] noncomputable def actAll (m x : Nat) : Bool :=
  (List.range m).all fun a => I.all (pactOne 11 4 m (ppw 11 4 x a))

end CertificateChecks.KernelKGC31M11

end
