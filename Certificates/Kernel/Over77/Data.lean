module

public import Certificates.Data.Kernel.Over77.Checks
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_ktree_gz CFSG.KD.Over77 T "Certificates/Kernel/Over77/data/t.bin.gz" 68 4
  548352 12540152032874293027

#kc_repo #kc_ktree_gz CFSG.KD.Over77 P "Certificates/Kernel/Over77/data/p.bin.gz" 68 4
  7480 4528540383247202531

#kc_repo #kc_ktree_gz CFSG.KD.Over77 X "Certificates/Kernel/Over77/data/x.bin.gz" 68 4
  5576 5276968619859022448

#kc_repo #kc_json_gz CFSG.KD.Over77 "Certificates/Kernel/Over77/data/gens.json.gz"
  2145 12543601339160913865 (S : List Nat) (A : Nat) (B : Nat) (Z : Nat) (Sig : Nat)

namespace CFSG.KD.Over77

open CFSG.KC.Over77

@[expose] noncomputable def mulR (i D : Nat) : Bool := mulK T P (nth S) i D

@[expose] noncomputable def clsR (i D : Nat) : Bool := clsK T P X i D

@[expose] noncomputable def pwR (p len W : Nat) : Bool := pwK A B Z P p len W

@[expose] noncomputable def swR (i len W : Nat) : Bool := swK A B Z X Sig i len W

end CFSG.KD.Over77

end
