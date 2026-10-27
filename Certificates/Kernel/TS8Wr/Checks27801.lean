module

public import Certificates.Data.Kernel.TS8WrK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.RowsForall
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.TS8Wr "Certificates/Kernel/TS8Wr/data/wr.json.gz" 32590
  9924191866242789355 (TB : Nat) (one : Nat) (RT : List (Nat × List Nat))
  (ZA : List (Nat × List Nat)) (ZC : List (Nat × Nat)) (AC : List (List (Nat × Nat)))

public section

namespace CFSG.KD.TS8Wr

open CFSG.KC.TS8WrK

theorem tb_ok : tbOK TB one = true := by decide +kernel

theorem p0_ok : CFSG.EvenSporadicStandard.Fin76b.TS8Wr.p0Ok () = true := by decide +kernel

theorem rt_ok : rtOK TB RT = true := by decide +kernel

theorem z_ok : zOK TB RT one ZA ZC = true := by decide +kernel

theorem za_ok : zaOK TB RT one ZA AC 349 = true := by decide +kernel

theorem neg_tb : notB (tbOK (TB + 1) one) = true := by decide +kernel

theorem neg_one : notB (tbOK TB 1) = true := by decide +kernel

theorem neg_root : notB (rtOK TB (RT.set 0 (0, 2 :: (rootsOf RT 0).tail))) = true := by
  decide +kernel

theorem neg_zc : notB (zOK TB RT one ZA (ZC.set 1 (4, 0))) = true := by decide +kernel

theorem neg_ac : notB (zaOK TB RT one ZA (AC.set 0 ((AC.getD 0 []).set 0 (4, 1))) 349) = true := by
  decide +kernel

theorem neg_count : notB (zaOK TB RT one ZA AC 348) = true := by decide +kernel

theorem neg_row : notB (rowChk TB RT one ZA 0 1 10) = true := by decide +kernel

theorem neg_pair : notB (pairsOK TB one one one [one]) = true := by decide +kernel

end CFSG.KD.TS8Wr

end

#kc_repo #kc_each_rows CFSG.KD.TS8Wr ch27801r
  (fun i z a => CFSG.KC.TS8WrK.rowChk CFSG.KD.TS8Wr.TB CFSG.KD.TS8Wr.RT CFSG.KD.TS8Wr.one
    CFSG.KD.TS8Wr.ZA i z a)
  "Certificates/Kernel/TS8Wr/data/rows.txt.gz" 3923 11856027218110311425 0 349

#kc_repo #kc_rows_forall CFSG.KD.TS8Wr.ch27801r_all
  (fun i z a => CFSG.KC.TS8WrK.rowChk CFSG.KD.TS8Wr.TB CFSG.KD.TS8Wr.RT CFSG.KD.TS8Wr.one
    CFSG.KD.TS8Wr.ZA i z a)
  "Certificates/Kernel/TS8Wr/data/rows.txt.gz" 3923 11856027218110311425 0 349
  CFSG.KD.TS8Wr.ch27801r
