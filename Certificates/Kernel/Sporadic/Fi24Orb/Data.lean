module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Fix.DataK
public import Certificates.Kernel.Fi23M.Data
public import Certificates.Data.Kernel.Spor.Fi24Orb

#kc_repo #kc_ktree_gz CFSG.KD.Fi24Orb FT "Certificates/Kernel/Sporadic/Fi24Orb/data/forest.bin.gz" 4096 4 2455488 3387048078537625248
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Orb OT "Certificates/Kernel/Sporadic/Fi24Orb/data/orbl.bin.gz" 4096 4 2455488 3999311635137771502
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Orb NMT "Certificates/Kernel/Sporadic/Fi24Orb/data/nmap.bin.gz" 3072 4 920808 3049134817580608774
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Orb NIT "Certificates/Kernel/Sporadic/Fi24Orb/data/ninv.bin.gz" 3072 4 920808 12773380927455324015
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Orb VTT "Certificates/Kernel/Sporadic/Fi24Orb/data/vt.bin.gz" 3072 4 920808 2807380586182027884
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Orb MX "Certificates/Kernel/Sporadic/Fi24Orb/data/m781.bin.gz" 152491 4 1677401 15296294309945869623
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Orb RS "Certificates/Kernel/Sporadic/Fi24Orb/data/m253.bin.gz" 16003 4 1952366 12683698904449394305
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Orb IJT "Certificates/Kernel/Sporadic/Fi24Orb/data/slp.bin.gz" 480 4 480 366595128995067008
#kc_repo #kc_json_gz CFSG.KD.Fi24Orb "Certificates/Kernel/Sporadic/Fi24Orb/data/words.json.gz" 369 300244679739114333
  (W1 : List Nat) (W2 : List Nat) (VW : List Nat)

public section

namespace CFSG.KD.Fi24Orb

@[expose] noncomputable def FD (r : Nat) : Nat :=
  fld(FT (Nat.shiftRight r (nat_lit 9)), Nat.mul (Nat.land r (nat_lit 511)) (nat_lit 64),
    nat_lit 18446744073709551615)

@[expose] noncomputable def OL (k : Nat) : Nat :=
  fld(OT (Nat.shiftRight k (nat_lit 9)), Nat.mul (Nat.land k (nat_lit 511)) (nat_lit 64),
    nat_lit 18446744073709551615)

@[expose] noncomputable def NM (k : Nat) : Nat :=
  fld(NMT (Nat.shiftRight k (nat_lit 10)), Nat.mul (Nat.land k (nat_lit 1023)) (nat_lit 24),
    nat_lit 16777215)

@[expose] noncomputable def NI (r : Nat) : Nat :=
  fld(NIT (Nat.shiftRight r (nat_lit 10)), Nat.mul (Nat.land r (nat_lit 1023)) (nat_lit 24),
    nat_lit 16777215)

@[expose] noncomputable def VT (r : Nat) : Nat :=
  fld(VTT (Nat.shiftRight r (nat_lit 10)), Nat.mul (Nat.land r (nat_lit 1023)) (nat_lit 24),
    nat_lit 16777215)

@[expose] noncomputable def IJ (k : Nat) : Nat :=
  fld(IJT (nat_lit 0), Nat.mul k (nat_lit 32), nat_lit 4294967295)

@[expose] noncomputable def R : Nat := CFSG.KD.Fi24Fix.R

@[expose] noncomputable def MUL3 : Nat → Nat → Nat := CFSG.KD.Fi23M.MUL

@[expose] noncomputable def VLD3 : Nat → Bool := CFSG.KD.Fi23M.VLD

end CFSG.KD.Fi24Orb

end
