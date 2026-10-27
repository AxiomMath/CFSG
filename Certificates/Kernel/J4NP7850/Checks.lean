module

public import Certificates.Data.Kernel.J4NP7850
public import Certificates.Kernel.J4NPVerdict.Defs
public import Certificates.Kernel.J4Q.VOrbData
public import CFSG.Quasithin.Vol2.KGFactC31J4M4Native
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelJ4NP7850 "Certificates/Kernel/J4NP7850/data/p7850.json.gz"
  19918 1651147187912352740
  (pv : List Nat) (mw : List Nat) (pr : List Nat) (k4 : Nat) (w : List (List Nat)) (P : List Nat)
  (b : List Nat) (R : List Nat) (Q : Nat) (u : List Nat) (q : List Nat)

namespace CertificateChecks.KernelJ4NP7850

open CFSG.KC.Loop CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4NPV CFSG.KD.J4M4F CFSG.KD.J4NP7850
  CFSG.Quasithin.KGC31.J4M4 CFSG.Sporadic.J4.Native

@[expose] noncomputable def G7850 : Nat := wordJ c rm one [A, B] [Ai, Bi] gWord

@[expose] noncomputable def Us7850 : List Nat := [U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10]

@[expose] noncomputable def FM7850 : List Nat :=
  [FM_0, FM_1, FM_2, FM_3, FM_4, FM_5, FM_6, FM_7, FM_8, FM_9]

@[expose] noncomputable def KW7850 : List Nat := kwVecs.map v2N

@[expose] noncomputable def TP7850 : List Nat := CFSG.Sporadic.J4.QT.letterRows.map packR

@[expose] noncomputable def S5L : List (List Nat) :=
  [S5_0, S5_1, S5_2, S5_3, S5_4, S5_5, S5_6, S5_7, S5_8, S5_9, S5_10, S5_11, S5_12, S5_13, S5_14]

@[expose] noncomputable def S6L : List (List Nat) :=
  [S6_0, S6_1, S6_2, S6_3, S6_4, S6_5, S6_6, S6_7, S6_8, S6_9, S6_10, S6_11, S6_12, S6_13, S6_14,
    S6_15, S6_16, S6_17, S6_18, S6_19, S6_20, S6_21, S6_22, S6_23, S6_24, S6_25, S6_26, S6_27]

theorem c7850_pi : piK rm G7850 pv KW7850 = true := by quickRfl

theorem c7850_y8fix : y8FixK rm Us7850 pv y8Bk = true := by quickRfl

theorem c7850_y8move : y8MoveK rm Us7850 pv cBk mw = true := by quickRfl

theorem c7850_y8dec : y8DecK y8Lk y8Bk cBk pr = true := by quickRfl

theorem c7850_move : moveK rm Us7850 pv k4 = true := by quickRfl

theorem c7850_orbLen : Nat.beq w.length 759 = true := by quickRfl

theorem c7850_orb : orbK TP7850 y8Bk w = true := by quickRfl

theorem c7850_kwFix : kwFixK rm one FM7850 KW7850 = true := by quickRfl

theorem c7850_rank :rankK c rm one FM7850 R Q = true := by quickRfl

theorem c7850_q : qK rm P Q = true := by quickRfl

theorem c7850_basis : basisK rm one FM7850 P b = true := by quickRfl

theorem c7850_span : spanK b KW7850 u = true := by quickRfl

theorem c7850_othV : othVK rm G7850 u q = true := by quickRfl

theorem c7850_othS : othSK (v2N rootV) q S5L S6L = true := by quickRfl

theorem c7850_duad : duadK c rm one G7850 FM7850 U4 = true := by quickRfl

theorem c7850_neg_rank : notB (rankK c rm one FM7850 (Nat.xor (R.headD 0) 1 :: R.tail) Q) = true := by
  quickRfl

theorem c7850_neg_kwFix : notB (kwFixK rm one (U4 :: FM7850.tail) KW7850) = true := by quickRfl

theorem c7850_neg_move :notB (moveK rm Us7850 pv 31) = true := by quickRfl

theorem c7850_neg_orb : notB (orbK TP7850 y8Bk w.reverse) = true := by quickRfl

theorem c7850_neg_othS : notB (othSK (v2N rootV) (S5_0.headD 0 :: q.tail) S5L S6L) = true := by
  quickRfl

theorem c7850_neg_span : notB (spanK b KW7850 u.tail) = true := by quickRfl

theorem c7850_neg_y8move : notB (y8MoveK rm Us7850 pv [1, 1, 1, 1, 1] mw) = true := by quickRfl

theorem c7850_neg_duad : notB (strictB (fRK c rm one FM7850 421) fun f =>
    Nat.beq (mulJ c rm G7850 f) (mulJ c rm U4 G7850)) = true := by quickRfl

end CertificateChecks.KernelJ4NP7850

end
