module

public import Certificates.Kernel.HS100.KDChecks
public import Certificates.Kernel.HS100.KDCls0
public import Certificates.Kernel.HS100.KDCls1
public import Certificates.Kernel.HS100.KDCls2
public import Certificates.Kernel.HS100.KDCls3
public import Certificates.Kernel.HS100.KDCls4
public import Certificates.Kernel.HS100.KDCls5
public import Certificates.Kernel.HS100.Chain
public import Certificates.Kernel.HS100.Five
public import Certificates.Kernel.LocalComp.ExcGlue
public import Certificates.Kernel.LocalQT.He4148.Glue
public import CFSG.Certificates.Kernel.LocalCompExcDerivSound
public import CFSG.Certificates.Kernel.SporSch.CodesImg
public import CFSG.Certificates.Kernel.SporSch.MathieuOC2Sound
public import CFSG.Certificates.Kernel.SporSch.ConjClosureSpec
public import CFSG.Certificates.Kernel.Child3Reps
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.LocalComp.ExcDeriv
open CFSG.LocalAnalysis.GLTheoremA.KD264HS CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu CFSG.KS.SporSch.MOC CFSG.KS.KeyBfs
open CFSG.ComponentClassification.J2Cover

#kc_forall_chunks kdAll (fun k => kdBlk k = true) 124 CertificateChecks.KernelHS100.kdBlk 1

theorem imgHA : imageList hsA = (unpack 100 7 (HP.F 0)).toList := by decide +kernel

theorem imgHB : imageList hsB = (unpack 100 7 (HP.F 1)).toList := by decide +kernel

theorem kdPerm : permOK 100 7 (mask 7) (100 * 7) (HP.F 0) (HPI 0) = true ∧
    permOK 100 7 (mask 7) (100 * 7) (HP.F 1) (HPI 1) = true := Bool.and_eq_true_iff.1 KD.perm

theorem hgS : ∀ j < hsS.length, imageList (hsS.getD j 1) = (unpack 100 7 (HP.F j)).toList := by
  intro j hj
  have hj2 : j < 2 := hj
  interval_cases j
  · exact imgHA
  · exact imgHB

theorem hpS : ∀ j < hsS.length, permOK 100 7 (mask 7) (100 * 7) (HP.F j) (HPI j) = true := by
  intro j hj
  have hj2 : j < 2 := hj
  interval_cases j
  · exact kdPerm.1
  · exact kdPerm.2

theorem kdId : imageList (1 : Equiv.Perm (Fin 100)) = (unpack 100 7 (pidn 100 7)).toList :=
  CertificateChecks.KernelLC.ExcGlue.one_img (CFSG.KC.BfsPin.idK_of_szOK hw)

theorem kdImg {wd : List Int} (h : lettersK 2 wd = true) :
    imageList (evalCodes hsS wd) = (unpack 100 7 (kdW wd)).toList :=
  CFSG.KS.SporSch.CodesImg.evalCodes_img hw hgS hpS kdId h

theorem arrHA : imgArr hsA = unpack 100 7 (HP.F 0) := by decide +kernel

theorem arrHB : imgArr hsB = unpack 100 7 (HP.F 1) := by decide +kernel

theorem gensOK : hsGensOK () = true := by
  unfold hsGensOK
  rw [arrHA, arrHB, siftP rfl (allN_spec KD.sift 0 (by norm_num)),
    siftP rfl (allN_spec KD.sift 1 (by norm_num))]
  rfl

theorem kdLetters : lettersK 2 zW = true ∧ lettersK 2 m1W = true ∧ lettersK 2 m2W = true ∧
    lettersK 2 m3W = true := by
  have h := KD.letters
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem mul_img {g h : Equiv.Perm (Fin 100)} {G H : Nat} (hg : imageList g = (unpack 100 7 G).toList)
    (hh : imageList h = (unpack 100 7 H).toList) :
    imageList (g * h) = (unpack 100 7 (kp G H)).toList := mulK_rep hw hg hh

theorem one_of {g : Equiv.Perm (Fin 100)} {G : Nat} (hg : imageList g = (unpack 100 7 G).toList)
    (h : Nat.beq G (pidn 100 7) = true) : g = 1 := by
  rw [Nat.eq_of_beq_eq_true h] at hg
  exact eq_of_img hg kdId

theorem eq_of {g h : Equiv.Perm (Fin 100)} {G H : Nat} (hg : imageList g = (unpack 100 7 G).toList)
    (hh : imageList h = (unpack 100 7 H).toList) (e : Nat.beq G H = true) : g = h := by
  rw [Nat.eq_of_beq_eq_true e] at hg
  exact eq_of_img hg hh

theorem moore : hsMooreOK () = true := by
  obtain ⟨lz, l1, l2, l3⟩ := kdLetters
  have iz := kdImg lz
  have i1 := kdImg l1
  have i2 := kdImg l2
  have i3 := kdImg l3
  have hz := KD.z
  simp only [Bool.and_eq_true] at hz
  obtain ⟨⟨-, z3⟩, zne⟩ := hz
  have hm := KD.moore
  simp only [Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, c1⟩, c2⟩, c3⟩ := hm
  have p3 : ∀ g : Equiv.Perm (Fin 100), g ^ 3 = g * g * g := fun g =>
    (pow_succ g 2).trans (by rw [sq])
  have p2 : ∀ g : Equiv.Perm (Fin 100), g ^ 2 = g * g := fun g => sq g
  unfold hsMooreOK
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [p3]; exact one_of (mul_img (mul_img iz iz) iz) z3
  · exact ne_of_neCK iz kdId zne
  · rw [p3]; exact one_of (mul_img (mul_img i1 i1) i1) a1
  · rw [p2]; exact one_of (mul_img i2 i2) a2
  · rw [p2]; exact one_of (mul_img i3 i3) a3
  · rw [p3]
    have i12 := mul_img i1 i2
    exact one_of (mul_img (mul_img i12 i12) i12) a4
  · rw [p3]
    have i23 := mul_img i2 i3
    exact one_of (mul_img (mul_img i23 i23) i23) a5
  · rw [p2]
    have i13 := mul_img i1 i3
    exact one_of (mul_img i13 i13) a6
  · exact ne_of_neCK i1 kdId a7
  · exact eq_of (mul_img i1 iz) (mul_img iz i1) c1
  · exact eq_of (mul_img i2 iz) (mul_img iz i2) c2
  · exact eq_of (mul_img i3 iz) (mul_img iz i3) c3

theorem kdGP : Nat.beq (KD3.GP 0) (HP.F 0) = true ∧ Nat.beq (KD3.GP 1) (HP.F 1) = true ∧
    permOK 100 7 (mask 7) (100 * 7) (HP.F 0) (KD3.GIP 0) = true ∧
    permOK 100 7 (mask 7) (100 * 7) (HP.F 1) (KD3.GIP 1) = true ∧
    canonK 100 7 (mask 7) (100 * 7) (KD3.GP 0) = true ∧ canonK 100 7 (mask 7) (100 * 7) (KD3.GIP 0) = true ∧
    canonK 100 7 (mask 7) (100 * 7) (KD3.GP 1) = true ∧
    canonK 100 7 (mask 7) (100 * 7) (KD3.GIP 1) = true := by
  have h := KD.gp
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩ := h
  exact ⟨a, b, c, d, e, f, g, i⟩

theorem kd_bind : (pairTables hsA hsB).size = 2 ∧ (pairTables hsA⁻¹ hsB⁻¹).size = 2 ∧
    ∀ l < 2, (pairTables hsA hsB)[l]! = arrTable 100 (unpack 100 7 (KD3.GP l)) ∧
      (pairTables hsA⁻¹ hsB⁻¹)[l]! = arrTable 100 (unpack 100 7 (KD3.GIP l)) := by
  obtain ⟨g0, g1, i0, i1, -⟩ := kdGP
  refine ⟨rfl, rfl, fun l hl => ?_⟩
  interval_cases l
  · refine ⟨?_, ?_⟩
    · change toTable hsA = _
      rw [Nat.eq_of_beq_eq_true g0]
      exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgHA
    · change toTable hsA⁻¹ = _
      exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (invK_rep imgHA i0)
  · refine ⟨?_, ?_⟩
    · change toTable hsB = _
      rw [Nat.eq_of_beq_eq_true g1]
      exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgHB
    · change toTable hsB⁻¹ = _
      exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (invK_rep imgHB i1)

theorem kd_canon : ∀ l < 2, canonK 100 7 (mask 7) (100 * 7) (KD3.GP l) = true ∧
    canonK 100 7 (mask 7) (100 * 7) (KD3.GIP l) = true := by
  obtain ⟨-, -, -, -, a, b, c, d⟩ := kdGP
  intro l hl
  interval_cases l
  · exact ⟨a, b⟩
  · exact ⟨c, d⟩

theorem kd_pos : ∀ c ∈ KD3.CS, 0 < c := by
  rw [KD.CS]
  decide

theorem kd_rep : ∀ j < KD3.N,
    repK 100 7 KD3.GP KD3.GIP 2 KD3.CS KD3.OFF KD3.CI KD3.E KD3.P KD3.L KD3.K KD3.S KD3.SI KD3.N
      130000 j = true := by
  intro j hj
  have hN := Nat.eq_of_beq_eq_true KD.N
  have hk : j / 1000 < 124 := by omega
  have h := kdAll (j / 1000) hk
  unfold kdBlk at h
  apply List.all_eq_true.1 h j
  rw [List.mem_range'_1]
  omega

theorem kd_hi : 0 < KD3.CS.length := by rw [KD.CS]; decide

theorem kd_cs0 : lget KD3.CS 0 = 123200 := by rw [KD.CS]; rfl

theorem kd_off0 : lget KD3.OFF 0 = 0 := by rw [KD.OFF]; rfl

theorem kd_x : toTable (evalCodes hsS zW) = arrTable 100 (unpack 100 7 (KD3.E (lget KD3.OFF 0))) := by
  have h := KD.z
  simp only [Bool.and_eq_true] at h
  rw [kd_off0, Nat.eq_of_beq_eq_true h.1.1]
  exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (kdImg kdLetters.1)

theorem classOK : hsClassOK () = true := by
  have hcl := closure_rep (n := 100) (w := 7) (cap := 130000) kd_bind kd_canon KD.off kd_rep kd_pos kd_hi
  have R := replay_class (n := 100) (w := 7) (cap := 130000) kd_bind kd_canon KD.off kd_rep kd_pos kd_hi
  have ht := conjTreeOK_of R
  have hk : keysDistinct 100 (Array.ofFn (n := lget KD3.CS 0)
      fun k => tabP 100 7 (KD3.E (lget KD3.OFF 0 + k.val))).toList = true := by
    apply CFSG.KS.SporSch.ClsSpec.keysDistinct_of
    rw [Array.toList_ofFn, List.map_ofFn, List.nodup_ofFn]
    intro a b e
    exact Fin.ext (R.inj a a.2 b b.2 e)
  unfold hsClassOK
  dsimp only
  rw [kd_x, hcl]
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, hk⟩, ?_⟩
  · convert ht using 3
  · rw [Array.size_ofFn, kd_cs0]
    rfl

theorem hsThreeKD : hsThreeOK () = true := by
  unfold hsThreeOK
  rw [gensOK, moore, classOK]
  rfl

end CertificateChecks.KernelHS100

end
