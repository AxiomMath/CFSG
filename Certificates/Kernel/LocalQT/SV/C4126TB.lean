module

public import Certificates.Kernel.LocalQT.SV.C4126T
public import CFSG.Certificates.Kernel.Misc.HexFlatSound

public section

namespace CFSG.KD.LQT.C4126

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

theorem hsCentTbl_eq {k : Nat} (hk : k < 43) :
    natArr (hsCentTbl k) = unpack 3850 12 (HC.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound HC.all (by norm_num) k hk
  rw [← HC.eq] at h
  exact h

theorem hsStrong_get {j : Nat} (hj : j < 2) : hsStrongArrs[j]! = unpack 3850 12 (HS.F j) := by
  unfold hsStrongArrs
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn, HS.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound HS.all j hj

end CFSG.KD.LQT.C4126

end
