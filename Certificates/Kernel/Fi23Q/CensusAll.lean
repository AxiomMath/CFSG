module

public import Certificates.Kernel.Fi23Q.ChkDefs
public import Certificates.Kernel.Fi23Q.CenDefs
import Certificates.Kernel.Fi23Q.Cos0
import Certificates.Kernel.Fi23Q.Cos1
import Certificates.Kernel.Fi23Q.Rep0
import Certificates.Kernel.Fi23Q.Rep1
import CFSG.Certificates.Kernel.Common.RowsForall
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_rows_forall CFSG.KD.Fi23Q.cos_all (fun i D => CFSG.KD.Fi23Q.cosK i D)
  "Certificates/Kernel/Fi23Q/data/cos.txt.gz" 126623 9225437296699062111 0 103 CFSG.KD.Fi23Q.cos

#kc_repo #kc_rows_forall CFSG.KD.Fi23Q.rep_all
  (fun ρ MV ncl CV WD XD => CFSG.KD.Fi23Q.repK ρ MV ncl CV WD XD)
  "Certificates/Kernel/Fi23Q/data/rep.txt.gz" 273730 9573150669597688594 0 145 CFSG.KD.Fi23Q.rep

namespace CFSG.KD.Fi23Q

open CFSG.KC.Pc3 CFSG.KC.Fi23Q

theorem cr_ok : ∀ q < 198, vecOK 13 (f32 CR q) = true := by decide +kernel

theorem pwA_zero : ∀ l < 5, f32 PW (8 + l) = 0 := by decide +kernel

theorem cjA_unit : ∀ l < 5, ∀ l' < 5, l < l' → f32 CJ (16 * (8 + l) + (8 + l')) = 4 ^ (8 + l') := by
  decide +kernel

theorem cjA_ok : ∀ k < 13, ∀ l < 5, k < 8 + l → aOK (f32 CJ (16 * k + (8 + l))) = true := by
  decide +kernel

theorem unit_ok : ∀ k < 13, vecOK 13 (4 ^ k) = true := by decide +kernel

theorem unitA_ok : ∀ l < 5, aOK (4 ^ (8 + l)) = true := by decide +kernel

end CFSG.KD.Fi23Q

end
