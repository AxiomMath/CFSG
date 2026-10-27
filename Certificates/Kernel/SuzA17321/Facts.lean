module

public import Certificates.Kernel.SuzA17321.Checks
public import Certificates.Kernel.SuzA17321.ChainFacts
public import Certificates.Kernel.SuzPump.PairFacts
public import CFSG.Certificates.Kernel.HeDihKSound
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
public import CFSG.Certificates.Kernel.Co3Five.TailSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzA17321

open CFSG.KS hiding levels
open CFSG.KC.Enum CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.HeDih CFSG.KC.BfsPin
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump
open CFSG.HardMathSupport.Dickson.I271.TabSuzA CFSG.HardMathSupport.Dickson.I271.TabSuzFuse
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.Certificates.Native CFSG.RankThree.PartOne CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2 (allLt_iff)

theorem pX : permB 1782 11 XP = true := pAll.1
theorem pU : permB 1782 11 UP = true := pAll.2.1
theorem pV : permB 1782 11 VP = true := pAll.2.2.1
theorem pT : permB 1782 11 TP = true := pAll.2.2.2.1
theorem pA : permB 1782 11 (AB 0) = true := pAll.2.2.2.2.1
theorem pB : permB 1782 11 (AB 1) = true := pAll.2.2.2.2.2

theorem hX : xAArr (levels ()) = unpack 1782 11 XP := by
  unfold xAArr
  exact rebuild_eq rbAll.1

theorem hU : rebuild (levels ()) uTuple = unpack 1782 11 UP := rebuild_eq rbAll.2.1
theorem hV : rebuild (levels ()) vTuple = unpack 1782 11 VP := rebuild_eq rbAll.2.2.1
theorem hT : rebuild (levels ()) tTuple = unpack 1782 11 TP := rebuild_eq rbAll.2.2.2

theorem hS (j : Nat) (hj : j < 11) : (aStrong ())[j]! = unpack 1782 11 (SAC.S j) :=
  binds.2.2.2.2.1 j hj

theorem hA : (aStrong ())[0]! = unpack 1782 11 (AB 0) := hS 0 (by norm_num)
theorem hB : (aStrong ())[1]! = unpack 1782 11 (AB 1) := hS 1 (by norm_num)

theorem inP_of {G : Nat} (h : siftPK G = true) : inP (levels ()) (unpack 1782 11 G) = true := by
  unfold siftPK at h
  simp only [Bool.and_eq_true] at h
  unfold inP CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.levels
  exact siftA_of Suz2306.binds Suz2306.perm SuzC.hl ⟨h.1.1, h.1.2, h.2⟩

theorem siftC_of {G : Nat} (h : siftCK G = true) :
    siftA 1782 (rawLevels 1782 (aStrong ()) aBase) aBase 0 (unpack 1782 11 G) = true := by
  unfold siftCK at h
  simp only [Bool.and_eq_true] at h
  exact siftA_of binds SAC.perm SAC.hl ⟨h.1.1, h.1.2, h.2⟩

theorem commX_of {P : Nat} (hp : permB 1782 11 P = true)
    (h : Nat.beq (cm 1782 11 P XP) (cm 1782 11 XP P) = true) :
    commA 1782 (unpack 1782 11 P) (unpack 1782 11 XP) = true := by
  unfold commA
  rw [comp_unpack' hw hp pX, comp_unpack' hw pX hp,
    eqA_unpack' hw (permB_pcomp hw hp pX) (permB_pcomp hw pX hp)]
  exact h

theorem c_size : ((aStrong ()).size == 11) = true := by
  rw [binds.2.2.2.1]
  rfl

theorem c_x : eqA 1782 (aStrong ())[2]! (xAArr (levels ())) = true := by
  rw [hS 2 (by norm_num), Nat.eq_of_beq_eq_true xS, hX]
  exact eqA_self _

theorem c_prod : ((rawOrbitSizes 1782 (aStrong ()) aBase).prod == 9797760) = true := by
  rw [orbits]
  rfl

theorem c_va : validA 1782 (aStrong ())[0]! = true := by
  rw [hA]
  exact validA_of pA

theorem c_vb : validA 1782 (aStrong ())[1]! = true := by
  rw [hB]
  exact validA_of pB

theorem c_pa : inP (levels ()) (aStrong ())[0]! = true := by
  rw [hA]
  exact inP_of siftP.1

theorem c_pb : inP (levels ()) (aStrong ())[1]! = true := by
  rw [hB]
  exact inP_of siftP.2.1

theorem c_ca : commA 1782 (aStrong ())[0]! (xAArr (levels ())) = true := by
  rw [hA, hX]
  exact commX_of pA commX.1

theorem c_cb : commA 1782 (aStrong ())[1]! (xAArr (levels ())) = true := by
  rw [hB, hX]
  exact commX_of pB commX.2

theorem c_rels (a b : Array Nat) (ha : a = unpack 1782 11 (AB 0))
    (hb : b = unpack 1782 11 (AB 1)) :
    CFSG.LieType.Multipliers.U43.rels.all (wordModX a b (xAArr (levels ()))) = true := by
  have hg : ∀ k < 2, (#[a, b] : Array (Array Nat))[k]! = unpack 1782 11 (AB k) := by
    intro k hk
    interval_cases k
    · exact ha
    · exact hb
  have hp : ∀ k < 2, PP 1782 11 (AB k) := by
    intro k hk
    interval_cases k
    · exact pp_of_permB hw pA
    · exact pp_of_permB hw pB
  have hxx := permB_pcomp hw pX pX
  rw [List.all_eq_true]
  intro wd hwd
  obtain ⟨h1, h2⟩ := evalWA_unpack hw hg hp wd
  unfold wordModX
  rw [h1, idA_eq hw, hX, comp_unpack' hw pX pX, eqA_PP h2 (PP.id hw),
    eqA_PP h2 (pp_of_permB hw pX), eqA_PP h2 (pp_of_permB hw hxx)]
  exact List.all_eq_true.1 relX wd hwd

theorem c_vu : validA 1782 (rebuild (levels ()) uTuple) = true := by
  rw [hU]
  exact validA_of pU

theorem c_vv : validA 1782 (rebuild (levels ()) vTuple) = true := by
  rw [hV]
  exact validA_of pV

theorem c_su : siftA 1782 (rawLevels 1782 (aStrong ()) aBase) aBase 0
    (rebuild (levels ()) uTuple) = true := by
  rw [hU]
  exact siftC_of siftC.1

theorem c_sv : siftA 1782 (rawLevels 1782 (aStrong ()) aBase) aBase 0
    (rebuild (levels ()) vTuple) = true := by
  rw [hV]
  exact siftC_of siftC.2

theorem c_uv : eqA 1782 (commutatorA 1782 (rebuild (levels ()) vTuple)
    (rebuild (levels ()) uTuple)) (xAArr (levels ())) = true := by
  have hc := permB_pcomp hw (permB_pcomp hw pV pU)
    (permB_pcomp hw (permB_pinvS hw pV) (permB_pinvS hw pU))
  rw [hU, hV, hX, commutator_unpack hw pV pU, eqA_unpack hw hc pX]
  exact commUV

theorem c_vt : validA 1782 (rebuild (levels ()) tTuple) = true := by
  rw [hT]
  exact validA_of pT

theorem c_pt : inP (levels ()) (rebuild (levels ()) tTuple) = true := by
  rw [hT]
  exact inP_of siftP.2.2

theorem c_t : eqA 1782 (conjA 1782 (rebuild (levels ()) tTuple) (xAArr (levels ())))
      (compA 1782 (xAArr (levels ())) (xAArr (levels ()))) = true := by
  have hc := permB_pcomp hw pT (permB_pcomp hw pX (permB_pinvS hw pT))
  rw [hT, hX, conj_unpack hw pT pX, comp_unpack hw pX pX,
    eqA_unpack hw hc (permB_pcomp hw pX pX)]
  exact conjT

theorem unpack_get' {P q : Nat} (hq : q < 1782) : (unpack 1782 11 P)[q]! = pg 11 (mask 11) P q := by
  rw [unpack, getElem!_pos _ q (by simpa using hq), Array.getElem_ofFn]

theorem c_base : allLt 5 (fun i => (xAArr (levels ()))[aBase[i]!]! == aBase[i]!) = true := by
  rw [hX, allLt_iff]
  intro i hi
  have e : aBase[i]! = i := by interval_cases i <;> rfl
  rw [e, unpack_get' (by omega)]
  exact Orb.allN_iff.1 fixB i hi

theorem fixEq (i : Nat) (hi : i < 6) :
    fixLevCount 1782 (levels ()) (xAArr (levels ())) i = fixXK i := by
  rw [hX]
  unfold CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.levels
  exact CFSG.KC.Misc.ChainTail.fixLevCount_eq Suz2306.binds Suz2306.perm SuzC.hl hi XP

theorem levEq : levCount 1782 (levels ()) 5 = CFSG.KC.PermWit.cntK 1782 (fun q =>
    Nat.blt (rpos 11 (mask 11) (1782 * 11) (SuzC.LR 5) q) (rcnt (SuzC.LR 5))) := by
  have hbl := Orb.base_lt_of_levels Suz2306.binds SuzC.hl
  obtain ⟨A, -⟩ := Orb.agree_levelK Suz2306.binds Suz2306.perm hbl (R := SuzC.LR) (TRI := SuzC.TRI)
    (by norm_num : 5 < 6) (SuzC.hl 5 (by norm_num))
  unfold levCount levList CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.levels
  rw [CFSG.KC.PermWit.cntK_eq, ← List.countP_eq_length_filter,
    ← List.map_coe_finRange_eq_range, List.countP_map]
  apply List.countP_congr
  intro q _
  have hqn := q.2
  simp only [Function.comp_apply]
  have hpos := A.pos q hqn
  have e2 : decide (((rawLevels 1782 smallStrongArrs smallBaseNat.toArray)[5]!).pos[(q : ℕ)]! <
      ((rawLevels 1782 smallStrongArrs smallBaseNat.toArray)[5]!).pts.size) =
      Nat.blt (rpos 11 (mask 11) (1782 * 11) (SuzC.LR 5) q) (rcnt (SuzC.LR 5)) := by
    apply Bool.eq_iff_iff.2
    rw [decide_eq_true_iff, Nat.blt_eq]
    exact hpos.symm
  rw [e2]

theorem c_fix (i k : Nat) (hi : i < 6) (h : Nat.beq (fixXK i) k = true) :
    (fixLevCount 1782 (levels ()) (xAArr (levels ())) i == k) = true := by
  rw [fixEq i hi, Nat.eq_of_beq_eq_true h]
  exact beq_self_eq_true _

theorem c_lev : (levCount 1782 (levels ()) 5 == 3) = true := by
  rw [levEq, Nat.eq_of_beq_eq_true cnt5]
  rfl

theorem caseA_ok : caseACheck () = true := by
  have hr := c_rels _ _ hA hB
  obtain ⟨f0, f1, f2, f3, f4⟩ := fixL
  have e0 := c_fix 0 162 (by norm_num) f0
  have e1 := c_fix 1 56 (by norm_num) f1
  have e2 := c_fix 2 10 (by norm_num) f2
  have e3 := c_fix 3 9 (by norm_num) f3
  have e4 := c_fix 4 8 (by norm_num) f4
  unfold caseACheck
  simp only [c_size, case_chain, c_x, c_prod, c_va, c_vb, c_pa, c_pb, c_ca, c_cb, hr, c_vu, c_vv,
    c_su, c_sv, c_uv, c_vt, c_pt, c_t, c_base, e0, e1, e2, e3, e4, c_lev, Bool.and_self]

end CertificateChecks.KernelSuzA17321

end
