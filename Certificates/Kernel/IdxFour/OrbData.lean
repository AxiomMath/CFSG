module

public import Certificates.Data.Kernel.IdxFourOrbitK
public import Certificates.Data.Kernel.IdxFourSiftK
public import CFSG.GF2Type.Smith1979.IdxFourModelE0Inputs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.GF2Type.Smith1979.GammaU.EnumDefs

public section

#kc_repo #kc_json_gz CFSG.KD.IF4O "Certificates/Kernel/IdxFour/data/e0orbit.json.gz" 65605
  6598323931543572269 (SP : Nat) (SI : Nat) (VT : Nat) (PS : Nat) (E : List (List Nat))

namespace CFSG.KD.IF4O

open CFSG.KC.IF4C CFSG.KC.IF4O CFSG.GF2Type.Smith1979.IdxFour

@[expose] noncomputable def blk (c : Nat) : Bool := blkOK SP VT PS 5 E0Chk.dCodes Orb.inO378b E c

@[expose] noncomputable def genOK (P Q g : Nat) : Bool :=
  Nat.beq (look P g) (CFSG.KC.IF4R.packR (E0Chk.sGensE0.getD g #[])) &&
    Nat.beq (mulP (look P g) (look Q g)) idP && Nat.beq (ap12 (look P g) 15) 15

@[expose] noncomputable def top : Bool := cntOK E 4092 && allBelow 5 (genOK SP SI)

end CFSG.KD.IF4O

end
