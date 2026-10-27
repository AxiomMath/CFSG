module

public import Certificates.Kernel.SporSch.Co2M.EnumQ
public import Certificates.Kernel.SporSch.Co2M.Six
public import CFSG.Sporadic.Co2Schreier.ThreeCheckInputs
public meta import Certificates.Kernel.SporSch.Co2M.EnumGen
public meta import CFSG.Sporadic.Co2Schreier.ThreeCheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert

meta def p0gRows : Array (Array Nat) :=
  p0Arrs.map fun a => Gen.rowsOf (Gen.matOf vecsM (Gen.basisOf vecsM) a)

meta def p0Recs : Array (Array Nat) :=
  Gen.enumRecs vecsM
    (p0gRows.map fun r => (List.range 22).foldl (fun a i => a ||| (r[i]! <<< (22 * i))) 0) 81

end CertificateChecks.KernelSporSch.Co2M

#kc_items CertificateChecks.KernelSporSch.Co2M.P0G include_bytes "data/EnumP0.P0G.items" 130 7903962285971444610
#kc_items CertificateChecks.KernelSporSch.Co2M.P0R include_bytes "data/EnumP0.P0R.items" 6413 16249391661111581775

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.Co2LE CFSG.Sporadic.Co2Schreier
open CFSG.KS.MatRep CFSG.RankThree.Native.F2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Co2Cert

@[expose] noncomputable def p0T : List (ℕ × ℕ) := p0Words.map (wP cT)

theorem p0g_ok : allN 2 (fun j => Nat.beq (P0G j) (p0T.getD j (0, 0)).1) = true := by
  decide +kernel

theorem p0head_ok : bAnd(Nat.beq (eM P0R 0) I22, Nat.beq (mR P0R 2 0) 1) = true := by quickRfl

theorem p0recs_ok : allN 81 (fun k => recK P0R P0G (PV 0) 2 81 k) = true := by quickRfl

@[expose] noncomputable def centM (k : ℕ) : List ℕ :=
  (List.range 81).filter fun j => Nat.beq (mmK (eM P0R k) (eM P0R j)) (mmK (eM P0R j) (eM P0R k))

theorem marked_ok : ((List.range 81).filter (fun k => decide (27 ≤ (centM k).length)) ==
    [0, 1, 3, 20, 22, 28, 30, 32, 34, 35, 39, 41, 43, 45, 46, 49, 50, 54, 56, 57,
      60, 61, 64, 68, 69, 72, 76]) = true := by
  quickRfl

theorem cube_ok :
    Nat.beq (mmK (mmK (eM P0R 4) (eM P0R 4)) (eM P0R 4)) I22 = false := by
  decide +kernel

@[expose] noncomputable def sixM (k : ℕ) (rows : List ℕ) : Bool :=
  allLt 6 fun j => vmul 22 co2PackedVecs[sixIdx j]! (eM P0R k) ^^^
    vmul 22 co2PackedVecs[sixAnchorIdx]! (eM P0R k) == xorBits sixPacked (colBits rows j)

theorem six_ok : (sixM 56 [1, 55, 49, 61, 63, 32] && sixM 1 [43, 34, 5, 14, 54, 45] &&
    sixM 20 [1, 57, 30, 20, 2, 7]) = true := by
  decide +kernel

theorem p0qcent_ok : ((List.range 512).filter (fun k =>
    Nat.beq (mmK (eM P0R 56) (eM QR k)) (mmK (eM QR k) (eM P0R 56))) == [0, 23]) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
