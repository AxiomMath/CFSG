
module

public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Gen
public import CFSG.RankThree.PartTwo.KFacts.KS14MultJ2Inputs
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Monster.B.Co2.PermArr
import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.RankThree.PartTwo.KFacts.KS14MultJ2Inputs
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.Certificates.Kernel.Spor.RawSlSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2M5

@[expose] def noWords : List (List Int) := []

end CertificateChecks.KernelMisc.J2M5

end

#ks_perm CertificateChecks.KernelMisc.J2M5.X 9 CFSG.RankThree.PartTwo.KFacts.KS14.j2x5Arr
#ks_perm CertificateChecks.KernelMisc.J2M5.Y 9 CFSG.RankThree.PartTwo.KFacts.KS14.j2y5Arr
#ks_perm CertificateChecks.KernelMisc.J2M5.G 9 CFSG.RankThree.PartTwo.KFacts.KS14.j2g5Arr
#ks_chars CertificateChecks.KernelMisc.J2M5.HP CFSG.RankThree.PartTwo.KFacts.KS14.cE25PtsHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2M5.HP CFSG.RankThree.PartTwo.KFacts.KS14.cE25PtsHex
  3 315 9 25
#ks_rawchain CertificateChecks.KernelMisc.J2M5.C 315 9 0 CFSG.ComponentClassification.J2Cover.autStrong
  CFSG.ComponentClassification.J2Cover.autBase 7 CertificateChecks.KernelMisc.J2M5.noWords

public section

namespace CertificateChecks.KernelMisc.J2M5

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexFlat CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.KFacts.KS14 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Mathieu
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (keyPts)
open CFSG.Monster.B.Co2 (allLt_iff)
open CFSG.KC.Misc.Clos (allN_iff)

@[expose] noncomputable def cm (p q : ℕ) : ℕ := pcomp 315 9 (mask 9) p q

@[expose] noncomputable def I : ℕ := pidn 315 9

theorem hx : j2x5Arr = unpack 315 9 X := arrBind_sound (by quickRfl)
theorem hy : j2y5Arr = unpack 315 9 Y := arrBind_sound (by quickRfl)
theorem hg : j2g5Arr = unpack 315 9 G := arrBind_sound (by quickRfl)

theorem hI : unpack 315 9 I = idA 315 := idK_sound (by quickRfl)

theorem cmp {p q : ℕ} (h : compEqK 315 9 (mask 9) (315 * 9) p q (cm p q) = true) :
    compA 315 (unpack 315 9 p) (unpack 315 9 q) = unpack 315 9 (cm p q) :=
  compEqK_sound h

theorem eqU {p q : ℕ} (h : eqK p q = true) : eqA 315 (unpack 315 9 p) (unpack 315 9 q) = true :=
  eqK_sound h

theorem c_perm : allN 7 (fun j => permOK 315 9 (mask 9) (315 * 9) (C.S j) (C.SI j)) = true := by
  quickRfl

theorem c_binds : Binds 315 9 C.S 7 3 C.BP autStrong autBase := by
  have hs : Nat.beq autStrong.size 7 = true := by quickRfl
  have hb : Nat.beq autBase.size 3 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j <;> exact arrBind_sound (by quickRfl)

theorem okA_of {p : ℕ} {a : Array ℕ} (ha : a = unpack 315 9 p)
    (hv : invEqK 315 9 (mask 9) (315 * 9) p (pinvS 315 9 (mask 9) p) = true)
    (hz : Nat.beq (Nat.shiftRight p (315 * 9)) 0 = true)
    (hs : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) C.LR C.TRI C.BP 3 0 p = true) :
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.okA a = true := by
  unfold CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.okA inP autLevels
  rw [Bool.and_eq_true]
  exact ⟨ha ▸ validA_unpack hv,
    siftK_soundR c_binds c_perm C.hl ha (Nat.eq_of_beq_eq_true hz) (range_of_permOK hv) hs⟩

theorem okx : CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.okA j2x5Arr = true :=
  okA_of hx (by quickRfl) (by quickRfl) (by quickRfl)
theorem oky : CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.okA j2y5Arr = true :=
  okA_of hy (by quickRfl) (by quickRfl) (by quickRfl)
theorem okg : CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.okA j2g5Arr = true :=
  okA_of hg (by quickRfl) (by quickRfl) (by quickRfl)

theorem pow_eq (p : ℕ) (k : ℕ) (hk : ∀ j < k, compEqK 315 9 (mask 9) (315 * 9) p
      (Nat.rec (motive := fun _ => ℕ) I (fun _ acc => cm p acc) j)
      (cm p (Nat.rec (motive := fun _ => ℕ) I (fun _ acc => cm p acc) j)) = true) :
    powArr 315 (unpack 315 9 p) k =
      unpack 315 9 (Nat.rec (motive := fun _ => ℕ) I (fun _ acc => cm p acc) k) := by
  induction k with
  | zero => exact hI.symm
  | succ k ih =>
    rw [powArr, ih fun j hj => hk j (Nat.lt_succ_of_lt hj)]
    exact cmp (hk k (Nat.lt_succ_self k))

@[expose] noncomputable def pw (p k : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) I (fun _ acc => cm p acc) k

theorem x5 : eqA 315 (powArr 315 j2x5Arr 5) (idA 315) = true := by
  rw [hx, pow_eq X 5 (by decide +kernel), ← hI]
  exact eqU (by quickRfl)

theorem xy : commA j2x5Arr j2y5Arr = true := by
  unfold commA
  rw [hx, hy, cmp (by quickRfl), cmp (by quickRfl)]
  exact eqU (by quickRfl)

theorem g_inv : invCand 315 (unpack 315 9 G) = unpack 315 9 (pinvS 315 9 (mask 9) G) :=
  (invEqK_sound (by quickRfl)).1

theorem gx : eqA 315 (conjA 315 j2g5Arr j2x5Arr) (powArr 315 j2x5Arr 4) = true := by
  unfold conjA
  rw [hx, hg, g_inv, cmp (by quickRfl), cmp (by quickRfl), pow_eq X 4 (by decide +kernel)]
  exact eqU (by quickRfl)

theorem gy : eqA 315 (conjA 315 j2g5Arr j2y5Arr) (compA 315 (powArr 315 j2x5Arr 3) j2y5Arr) =
    true := by
  unfold conjA
  rw [hx, hy, hg, g_inv, cmp (by quickRfl), cmp (by quickRfl), pow_eq X 3 (by decide +kernel),
    cmp (by quickRfl)]
  exact eqU (by quickRfl)

theorem pts_get (i : ℕ) (hi : i < 25) : cE25.pts[i]! = unpack 315 9 (HP.F i) := by
  change cE25Lit.pts[i]! = _
  unfold cE25Lit
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, HP.eq]
  exact hexTable3_sound HP.all i hi

@[expose] noncomputable def GE (k : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) X (fun _ _ => Y) k

theorem gens_get (k : ℕ) (hk : k < 2) : gensE25[k]! = unpack 315 9 (GE k) := by
  interval_cases k
  · exact hx
  · exact hy

theorem e_head : headK 315 9 2 25 GE HP.F = true := by quickRfl

@[expose] noncomputable def EE (i k : ℕ) : ℕ := (cE25.edges[i]!)[k]!

@[expose] noncomputable def EP (i : ℕ) : ℕ := cE25.par[i]!

@[expose] noncomputable def EL (i : ℕ) : ℕ := cE25.lab[i]!

theorem e_points : ∀ i < 25, pointK 315 9 2 25 GE HP.F EE EP EL i = true := by
  have h : pointsK 315 9 2 25 GE HP.F EE EP EL 0 25 = true := by quickRfl
  intro i hi
  have := (allN_iff _ _).1 h i hi
  have e : Nat.add 0 i = i := Nat.zero_add i
  rwa [e] at this

theorem e_keys : ∀ i < 25, ∀ j < i, keyK 315 9 keyPts (HP.F i) ≠ keyK 315 9 keyPts (HP.F j) := by
  have h : keysK 315 9 keyPts HP.F 0 25 = true := by quickRfl
  intro i hi j hj he
  have e : Nat.add 0 i = i := Nat.zero_add i
  have h1 := (allN_iff _ _).1 h i hi
  rw [e] at h1
  have h2 := (allN_iff _ _).1 h1 j hj
  rw [he, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem enum : enumOK 315 gensE25 keyPts cE25 = true :=
  enumK_sound (G := GE) (PT := HP.F) (by quickRfl) (by decide) (by decide +kernel) gens_get
    (by decide +kernel) pts_get
    (fun i hi => ⟨by revert i; decide +kernel, fun _ _ => rfl⟩) (fun _ _ => ⟨rfl, rfl⟩)
    e_head e_points e_keys

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.KS14 CFSG.Blueprint CFSG.ComponentClassification.J2Cover
  CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
open Certificates in
theorem facts : chkMult5 = true := by
  have hsz : cE25.pts.size = 25 := by
    change cE25Lit.pts.size = 25
    simp [cE25Lit]
  unfold chkMult5
  rw [okx, oky, okg, x5, xy, gx, gy, enum, hsz]
  rfl

end CertificateChecks.KernelMisc.J2M5

end
