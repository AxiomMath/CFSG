module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Orb.Data
public import Certificates.Data.Kernel.Spor.Fi24Net
public import Certificates.Data.CFSGNative.Fi24.Data

#kc_repo #kc_ktree CFSG.KD.Fi24Net N0 "Certificates/Kernel/Sporadic/Fi24Net/data/net0.bin" 65536 4 2424832 6711677265457577549
#kc_repo #kc_ktree CFSG.KD.Fi24Net N1 "Certificates/Kernel/Sporadic/Fi24Net/data/net1.bin" 65536 4 2424832 13237910955367019884
#kc_repo #kc_ktree CFSG.KD.Fi24Net N2 "Certificates/Kernel/Sporadic/Fi24Net/data/net2.bin" 65536 4 2424832 12563756317721825114
#kc_repo #kc_ktree CFSG.KD.Fi24Net N3 "Certificates/Kernel/Sporadic/Fi24Net/data/net3.bin" 65536 4 2424832 1186358309835032708
#kc_repo #kc_ktree CFSG.KD.Fi24Net N4 "Certificates/Kernel/Sporadic/Fi24Net/data/net4.bin" 65536 4 2424832 10993685834993223862
#kc_repo #kc_ktree CFSG.KD.Fi24Net N5 "Certificates/Kernel/Sporadic/Fi24Net/data/net5.bin" 65536 4 2424832 5935693814338439431
#kc_repo #kc_ktree CFSG.KD.Fi24Net N6 "Certificates/Kernel/Sporadic/Fi24Net/data/net6.bin" 65536 4 2424832 14381874023273625519
#kc_repo #kc_ktree CFSG.KD.Fi24Net N7 "Certificates/Kernel/Sporadic/Fi24Net/data/net7.bin" 65536 4 2424832 11289805448707245438
#kc_repo #kc_ktree CFSG.KD.Fi24Net N8 "Certificates/Kernel/Sporadic/Fi24Net/data/net8.bin" 65536 4 2424832 12480879332998963255
#kc_repo #kc_ktree CFSG.KD.Fi24Net N9 "Certificates/Kernel/Sporadic/Fi24Net/data/net9.bin" 65536 4 2424832 1829235019667799033
#kc_repo #kc_ktree CFSG.KD.Fi24Net N10 "Certificates/Kernel/Sporadic/Fi24Net/data/net10.bin" 65536 4 2424832 18134496867124630968
#kc_repo #kc_ktree CFSG.KD.Fi24Net N11 "Certificates/Kernel/Sporadic/Fi24Net/data/net11.bin" 65536 4 2424832 734299909962486796
#kc_repo #kc_ktree CFSG.KD.Fi24Net N12 "Certificates/Kernel/Sporadic/Fi24Net/data/net12.bin" 65536 4 2424832 3017109447996526668

public section

namespace CFSG.KD.Fi24Net

open CFSG.KC CFSG.KC.Fi24Net

@[expose] noncomputable def NW (j l : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 7),
    nIf(Nat.blt j (nat_lit 3),
      nIf(Nat.beq j (nat_lit 0), N0 l, nIf(Nat.beq j (nat_lit 1), N1 l, N2 l)),
      nIf(Nat.beq j (nat_lit 3), N3 l, nIf(Nat.beq j (nat_lit 4), N4 l,
        nIf(Nat.beq j (nat_lit 5), N5 l, N6 l)))),
    nIf(Nat.beq j (nat_lit 7), N7 l, nIf(Nat.beq j (nat_lit 8), N8 l,
      nIf(Nat.beq j (nat_lit 9), N9 l, nIf(Nat.beq j (nat_lit 10), N10 l,
        nIf(Nat.beq j (nat_lit 11), N11 l, nIf(Nat.beq j (nat_lit 12), N12 l, nat_lit 0)))))))

@[expose] noncomputable def nthW (l : List (List Int)) (j : Nat) : List Int :=
  List.rec (motive := fun _ => Nat → List Int) (fun _ => List.nil)
    (fun a _ ih j => Nat.rec (motive := fun _ => List Int) a (fun k _ => ih k) j) l j

@[expose] noncomputable def WD (j : Nat) : List Int :=
  nthW (CFSG.Sporadic.Fi24.Native.chainWords ()).toList j

@[expose] noncomputable def nck (j : Nat) : Bool := netOK (NW j)

@[expose] noncomputable def gck (g : Nat) : Bool :=
  (fun t => genOK CFSG.KD.Fi24Orb.OT (NW t) (Nat.mul (nat_lit 19) t) (Nat.mod g (nat_lit 19)))
    (Nat.div g (nat_lit 19))

@[expose] noncomputable def wck (g : Nat) : Bool :=
  (fun j => wordOK NW (WD j) j (Nat.mod g (nat_lit 19))) (Nat.add (nat_lit 2) (Nat.div g (nat_lit 19)))

end CFSG.KD.Fi24Net

end
