module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.Misc.Perm.HexTabCmd
public import CFSG.Certificates.Kernel.Misc.HexRowsSound
public import CFSG.Certificates.Kernel.Spor.RowSound
public import CFSG.Sporadic.SuzOddCore.Arrays
meta import CFSG.Sporadic.SuzOddCore.Arrays
import all CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Spor.RawSlSound
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzCertT CFSG.Sporadic.SuzOddCore.certChainText

#kmisc_hexflat_tab CertificateChecks.KernelSpor.SuzCertT CFSG.Sporadic.SuzOddCore.certChainText
  4 32 15 8580

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore

meta def rowsOf (r : Nat) (t : Array Nat) : Array (Array Nat) :=
  (List.range r).toArray.map fun j => t.extract (32 * j) (32 * j + 32)

meta def certInvRowsM : Array (Array Nat) :=
  ((List.range 12).toArray.map fun k =>
    rowsOf 715 (CFSG.Monster.B.Co2.Native.invCand 22880 (certArr k))).flatten

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.SuzCertI CertificateChecks.KernelSpor.OddCore.certInvRowsM
  15

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Row

theorem certP0 : CFSG.KC.Misc.HexFlat.run 4 32 15 715 SuzCertT.F
    (CFSG.KC.Misc.HexFlat.dropL 0 (CFSG.KC.Misc.HexFlat.dropL 0
      (CFSG.KC.Misc.HexFlat.dropL 0 SuzCertT.chars))) 0 0 0 0 0 = true := by quickRfl
theorem certP1 : CFSG.KC.Misc.HexFlat.run 4 32 15 1430 SuzCertT.F
    (CFSG.KC.Misc.HexFlat.dropL 0 (CFSG.KC.Misc.HexFlat.dropL 0
      (CFSG.KC.Misc.HexFlat.dropL 91520 SuzCertT.chars))) 715 0 0 0 0 = true := by quickRfl
theorem certP2 : CFSG.KC.Misc.HexFlat.run 4 32 15 2145 SuzCertT.F
    (CFSG.KC.Misc.HexFlat.dropL 0 (CFSG.KC.Misc.HexFlat.dropL 0
      (CFSG.KC.Misc.HexFlat.dropL 183040 SuzCertT.chars))) 1430 0 0 0 0 = true := by quickRfl
theorem certP3 : CFSG.KC.Misc.HexFlat.run 4 32 15 2860 SuzCertT.F
    (CFSG.KC.Misc.HexFlat.dropL 0 (CFSG.KC.Misc.HexFlat.dropL 0
      (CFSG.KC.Misc.HexFlat.dropL 274560 SuzCertT.chars))) 2145 0 0 0 0 = true := by quickRfl
theorem certP4 : CFSG.KC.Misc.HexFlat.run 4 32 15 3575 SuzCertT.F
    (CFSG.KC.Misc.HexFlat.dropL 0 (CFSG.KC.Misc.HexFlat.dropL 0
      (CFSG.KC.Misc.HexFlat.dropL 366080 SuzCertT.chars))) 2860 0 0 0 0 = true := by quickRfl
theorem certP5 : CFSG.KC.Misc.HexFlat.run 4 32 15 4290 SuzCertT.F
    (CFSG.KC.Misc.HexFlat.dropL 0 (CFSG.KC.Misc.HexFlat.dropL 57601
      (CFSG.KC.Misc.HexFlat.dropL 399999 SuzCertT.chars))) 3575 0 0 0 0 = true := by quickRfl
theorem certP6 : CFSG.KC.Misc.HexFlat.run 4 32 15 5005 SuzCertT.F
    (CFSG.KC.Misc.HexFlat.dropL 0 (CFSG.KC.Misc.HexFlat.dropL 149121
      (CFSG.KC.Misc.HexFlat.dropL 399999 SuzCertT.chars))) 4290 0 0 0 0 = true := by quickRfl
theorem certP7 : CFSG.KC.Misc.HexFlat.run 4 32 15 5720 SuzCertT.F
    (CFSG.KC.Misc.HexFlat.dropL 0 (CFSG.KC.Misc.HexFlat.dropL 240641
      (CFSG.KC.Misc.HexFlat.dropL 399999 SuzCertT.chars))) 5005 0 0 0 0 = true := by quickRfl
theorem certP8 : CFSG.KC.Misc.HexFlat.run 4 32 15 6435 SuzCertT.F
    (CFSG.KC.Misc.HexFlat.dropL 0 (CFSG.KC.Misc.HexFlat.dropL 332161
      (CFSG.KC.Misc.HexFlat.dropL 399999 SuzCertT.chars))) 5720 0 0 0 0 = true := by quickRfl
theorem certP9 : CFSG.KC.Misc.HexFlat.run 4 32 15 7150 SuzCertT.F
    (CFSG.KC.Misc.HexFlat.dropL 23682 (CFSG.KC.Misc.HexFlat.dropL 399999
      (CFSG.KC.Misc.HexFlat.dropL 399999 SuzCertT.chars))) 6435 0 0 0 0 = true := by quickRfl
theorem certP10 : CFSG.KC.Misc.HexFlat.run 4 32 15 7865 SuzCertT.F
    (CFSG.KC.Misc.HexFlat.dropL 115202 (CFSG.KC.Misc.HexFlat.dropL 399999
      (CFSG.KC.Misc.HexFlat.dropL 399999 SuzCertT.chars))) 7150 0 0 0 0 = true := by quickRfl
theorem certP11 : CFSG.KC.Misc.HexFlat.run 4 32 15 8580 SuzCertT.F
    (CFSG.KC.Misc.HexFlat.dropL 206722 (CFSG.KC.Misc.HexFlat.dropL 399999
      (CFSG.KC.Misc.HexFlat.dropL 399999 SuzCertT.chars))) 7865 0 0 0 0 = true := by quickRfl

open CFSG.KC.Misc.HexFlat in
theorem certRows : RowsW SuzCertT.chars 4 32 15 SuzCertT.F 0 8580 :=
  rowsW_cat (rowsW_of_run (by decide) (by decide) (by decide) (by decide) certP0)
    (rowsW_cat (rowsW_of_run (by decide) (by decide) (by decide) (by decide) certP1)
    (rowsW_cat (rowsW_of_run (by decide) (by decide) (by decide) (by decide) certP2)
    (rowsW_cat (rowsW_of_run (by decide) (by decide) (by decide) (by decide) certP3)
    (rowsW_cat (rowsW_of_run (by decide) (by decide) (by decide) (by decide) certP4)
    (rowsW_cat (rowsW_of_run (by decide) (by decide) (by decide) (by decide) certP5)
    (rowsW_cat (rowsW_of_run (by decide) (by decide) (by decide) (by decide) certP6)
    (rowsW_cat (rowsW_of_run (by decide) (by decide) (by decide) (by decide) certP7)
    (rowsW_cat (rowsW_of_run (by decide) (by decide) (by decide) (by decide) certP8)
    (rowsW_cat (rowsW_of_run (by decide) (by decide) (by decide) (by decide) certP9)
    (rowsW_cat (rowsW_of_run (by decide) (by decide) (by decide) (by decide) certP10)
    ((rowsW_of_run (by decide) (by decide) (by decide) (by decide) certP11))))))))))))

theorem certArr_eq {k : Nat} (hk : k < 12) : certArr k = rowArr 22880 15 SuzCertT.F (715 * k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_rows_of (d := 4) (w := 15) (N := 8580) (r := 715)
    (k := k) (CFSG.KC.Misc.HexFlat.hexTable_of_rowsW (by decide) (by decide) certRows) (by omega)
  rw [← SuzCertT.eq] at h
  exact h

@[expose] noncomputable def certPerm (k : Nat) : Bool :=
  rpermK 22880 15 (mask 15) SuzCertT.F (Nat.mul 715 k) SuzCertI (Nat.mul 715 k)

#kc_each certPerm 0 12

theorem cert_perms : allN 12 (fun k =>
    rpermK 22880 15 (mask 15) SuzCertT.F (Nat.mul 715 k) SuzCertI (Nat.mul 715 k)) = true :=
  CFSG.KS.Raw.allN_of_forall fun k hk => by
    interval_cases k
    exacts [certPerm0, certPerm1, certPerm2, certPerm3, certPerm4, certPerm5, certPerm6, certPerm7,
      certPerm8, certPerm9, certPerm10, certPerm11]

end CertificateChecks.KernelSpor.OddCore

end
