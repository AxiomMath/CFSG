module

public import Certificates.Data.Kernel.F4Planes
public import Certificates.Kernel.F4Syl3.ModelChk
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CFSG.KD.F4Planes "Certificates/Kernel/F4Planes/data/model.json.gz" 26952
  4247695855319381425 (VT : Nat) (AT : Nat) (QT : Nat) (OM : Nat) (PR : Nat) (rows : List (List (Nat × Nat × Nat)))

#kc_each CFSG.KD.F4Planes.ch14950pl r (fun k => CFSG.KC.F4Planes.rowK CFSG.KD.F4Planes.VT
  CFSG.KD.F4Planes.AT CFSG.KD.F4Planes.QT CFSG.KD.F4Planes.OM CFSG.KD.F4Planes.PR
  CFSG.KD.F4Syl3.reps CFSG.KD.F4Planes.rows k) 0 48

namespace CFSG.KD.F4Planes

open CFSG.KC.F4Planes

theorem tab_ok : tabChk VT AT QT = true := by quickRfl

theorem om_ok : omChk VT AT QT OM = true := by quickRfl

theorem rep_ok : repChk VT AT QT PR = true := by quickRfl

theorem rows_len : Nat.beq rows.length 48 = true := by quickRfl

theorem neg_tab : (!tabChk (Nat.xor VT (Nat.shiftLeft 1 45920)) AT QT) = true := by quickRfl
theorem neg_om : (!omChk VT AT QT (Nat.xor OM 2)) = true := by quickRfl

theorem neg_rep : (!repChk VT AT QT (Nat.xor PR 1024)) = true := by quickRfl

theorem neg_rep_range : (!repChk VT AT QT (Nat.add PR 440)) = true := by quickRfl

theorem neg_row : (!rowK VT AT QT OM PR CFSG.KD.F4Syl3.reps (rows.map List.tail) 0) = true := by
  quickRfl

theorem neg_row_u : (!rowK VT AT QT OM PR (CFSG.KD.F4Syl3.reps.map (· + 1)) rows 0) = true := by
  quickRfl

end CFSG.KD.F4Planes

end
