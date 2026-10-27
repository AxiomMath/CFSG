module

public import Certificates.Kernel.Fi22Twist.TxPerm
public import CFSG.Certificates.Kernel.Fi22Rk.Side
public import Certificates.Data.Fi22Twist

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative

theorem szTX : szOK 3510 12 = true := by decide

theorem hexNums_sameX (d : Nat) (s : String) :
    hexNums d s = CFSG.Sporadic.FischerOddCore.hexNums d s := rfl

theorem rowsOf_sameX (m : Nat) (a : Array Nat) :
    rowsOf m a = CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.rowsOf m a := rfl

theorem repXYZ_eq : repXYZ = CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.rowsOf 3510
    (unpack (3510 * 15) 12 TX.F) := by
  have e : repXYZ = rowsOf 3510 (hexNums 3 repXYZHex) := rfl
  rw [e, rowsOf_sameX, hexNums_sameX, CFSG.KS.HexNums.hexNums_of TX.eq TX.ok]

theorem repXYZ_facts : repXYZ.size = 15 ∧
    ∀ k < 15, repXYZ[k]! = unpack 3510 12 (rowR TX.F k) ∧ PP 3510 12 (rowR TX.F k) := by
  rw [repXYZ_eq]
  exact CFSG.KC.Fi22RkS.rows_of (by norm_num) szTX ch431009tx

theorem repXYZ_ap {k i : Nat} (hk : k < 15) (hi : i < 3510) :
    (repXYZ[k]!)[i]! = ap (rowR TX.F k) i := by
  rw [(repXYZ_facts.2 k hk).1, CFSG.KC.Fi22RkS.get_unpack hi]
  rfl

end CertificateChecks.KernelFi22Twist

end
