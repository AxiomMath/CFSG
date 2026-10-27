module

public import Certificates.Data.Kernel.ThCent.Defs
public import Certificates.Kernel.ThCent.Data
public import CFSG.Certificates.Kernel.Th.S.Data.DB_Sel
public import Certificates.Kernel.SporSch.Ru.RowsGen

public section

namespace CFSG.KD.ThCent.Chk

open CFSG.KC.Th CFSG.KC.ThCent

theorem shared : sharedOK ThB.LT BF ThA.CB CJ ThB.om = true := by decide +kernel

@[expose] noncomputable def svF (i : Nat) : Bool :=
  svChunk SV PI ThB.OB ThB.osh ThB.owd ThB.om ThB.NO i

@[expose] noncomputable def ptF (i : Nat) : Bool :=
  ptChunk SV QI ThB.OB ThB.osh ThB.owd ThB.om ThB.NO i

#kss_each CFSG.KD.ThCent.Chk.sv CFSG.KD.ThCent.Chk.svF 9
#kss_each CFSG.KD.ThCent.Chk.pt CFSG.KD.ThCent.Chk.ptF 9

end CFSG.KD.ThCent.Chk

end
