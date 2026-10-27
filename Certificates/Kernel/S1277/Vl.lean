module

public import Certificates.Data.Kernel.S1277KVl
public import Certificates.Kernel.S1277.ModData
public import Certificates.Kernel.S1277.LatData
public import Certificates.Kernel.S1277.FrData
public import Certificates.Kernel.S1277.SvData
public import Certificates.Kernel.S1277.VlData
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KP.S1277Vl

open CFSG.KC.S1277Lat CFSG.KC.S1277Vl CFSG.KD.S1277Mod CFSG.KD.S1277Lat CFSG.KD.S1277Fr
  CFSG.KD.S1277Sv CFSG.KD.S1277Vl

noncomputable abbrev Mn : Mdl := ⟨48, apn, cpn, ipn, onen⟩

theorem vl_nx : sgin.getD 4 0 = 14 ∧ nxn.getD 14 0 = 7 := by decide +kernel

theorem vl_e : eChk Mn (ngn.getD 14 []) (ntn.getD 14 []) (sgpn.getD 4 0) (onen * 64 + 5) = true := by
  quickRfl

theorem vl_a1 : vlChk a1 (b1.getD 0 []) (b1.getD 1 []) = true := by quickRfl

theorem vl_a2 : vlChk a2 (b2.getD 0 []) (b2.getD 1 []) = true := by quickRfl

theorem vl_ab1 : abChk Mn (ntn.getD 14 []) (sgcn.getD 4 0) (b1.getD 0 []) = true ∧
    abChk Mn (ntn.getD 14 []) (sgcn.getD 4 0) (b1.getD 1 []) = true := by
  constructor <;> quickRfl

theorem vl_ab2 : abChk Mn (ntn.getD 14 []) (sgcn.getD 4 0) (b2.getD 0 []) = true ∧
    abChk Mn (ntn.getD 14 []) (sgcn.getD 4 0) (b2.getD 1 []) = true := by
  constructor <;> quickRfl

end CFSG.KP.S1277Vl

end
