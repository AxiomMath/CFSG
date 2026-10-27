module

public import Certificates.Kernel.LocalComp.Fi24TwoB.A15027
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeCheck
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U43Action

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Fi24Shape

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.ConjTree
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime CertificateChecks.KernelSpor.Fi24C
open CertificateChecks.KernelSpor CertificateChecks.KernelLC CertificateChecks.KernelLC.Fi24B
open CFSG.Sporadic.FischerOddCore (fi24PStrong)
open CFSG.EvenSporadicStandard.TwoFi22.DS81

theorem siftZ : siftK 504 9 (mask 9) (504 * 9) (pidn 504 9) Fi24BKd.LR Fi24BKd.TRI Fi24BKd.BP 7 0
    (wordK fi24ShapeZ) = true := by quickRfl
theorem siftX : siftK 504 9 (mask 9) (504 * 9) (pidn 504 9) Fi24BKd.LR Fi24BKd.TRI Fi24BKd.BP 7 0
    (wordK fi24ShapeX) = true := by quickRfl
theorem siftY : siftK 504 9 (mask 9) (504 * 9) (pidn 504 9) Fi24BKd.LR Fi24BKd.TRI Fi24BKd.BP 7 0
    (wordK fi24ShapeY) = true := by quickRfl

theorem sift_of {w : List Int}
    (h : siftK 504 9 (mask 9) (504 * 9) (pidn 504 9) Fi24BKd.LR Fi24BKd.TRI Fi24BKd.BP 7 0
      (wordK w) = true) : fi24SiftW w = true := by
  obtain ⟨w1, w2⟩ := word_eq w
  unfold fi24SiftW fi24KdLevels
  rw [dS, siftK_eq bindsD permD Fi24BKd.hl w1 (hi_of w2) (range_of_canonK w2)]
  exact h

@[expose] noncomputable def pLetK (z : Int) : Nat :=
  if z = 1 then Fi24PC.S 0 else if z = -1 then Fi24PC.SI 0 else if z = 2 then Fi24PC.S 1
  else Fi24PC.SI 1

@[expose] noncomputable def pWordK (w : List Int) : Nat :=
  w.foldr (fun z t => pcomp 378 9 (mask 9) (pLetK z) t) (pidn 378 9)

theorem pIdK : idK 378 9 (mask 9) = true := by quickRfl
theorem pIdC : canonK 378 9 (mask 9) (378 * 9) (pidn 378 9) = true := by quickRfl
theorem pCn : allN 2 (fun j => bAnd(canonK 378 9 (mask 9) (378 * 9) (Fi24PC.S j),
    canonK 378 9 (mask 9) (378 * 9) (Fi24PC.SI j))) = true := by quickRfl

theorem pCn' {j : Nat} (hj : j < 2) : Cn 378 9 (Fi24PC.S j) ∧ Cn 378 9 (Fi24PC.SI j) :=
  (bAnd_iff _ _).1 (allN_spec pCn j hj)

theorem pStrong {j : Nat} (hj : j < 10) : fi24PStrong[j]! = unpack 378 9 (Fi24PC.S j) := by
  rw [pS]
  exact ofFn_get hj

theorem pInv {j : Nat} (hj : j < 10) :
    invCand 378 fi24PStrong[j]! = unpack 378 9 (Fi24PC.SI j) := by
  rw [pStrong hj]
  exact (invEqK_sound (allN_spec permP j hj)).1

theorem pLetter_eq (z : Int) : fi24PLetterA z = unpack 378 9 (pLetK z) ∧ Cn 378 9 (pLetK z) := by
  unfold fi24PLetterA pLetK
  split_ifs
  · exact ⟨pStrong (by norm_num), (pCn' (by norm_num)).1⟩
  · exact ⟨pInv (by norm_num), (pCn' (by norm_num)).2⟩
  · exact ⟨pStrong (by norm_num), (pCn' (by norm_num)).1⟩
  · exact ⟨pInv (by norm_num), (pCn' (by norm_num)).2⟩

theorem pWord_eq : ∀ w : List Int, fi24PWordA w = unpack 378 9 (pWordK w) ∧ Cn 378 9 (pWordK w)
  | [] => ⟨(idK_sound pIdK).symm, pIdC⟩
  | z :: w => by
    obtain ⟨ih1, ih2⟩ := pWord_eq w
    obtain ⟨l1, l2⟩ := pLetter_eq z
    have e : fi24PWordA (z :: w) = compA 378 (fi24PLetterA z) (fi24PWordA w) := rfl
    have e2 : pWordK (z :: w) = pcomp 378 9 (mask 9) (pLetK z) (pWordK w) := rfl
    rw [e, e2, ih1, l1, compA_unpack l2 ih2]
    exact ⟨rfl, canonK_pcomp l2 ih2⟩

@[expose] noncomputable def relK (X Xi Y Yi : Nat) (v : List (Fin 2 × Bool)) : Nat :=
  v.foldr (fun l t => pcomp 378 9 (mask 9) (if l.1.val = 0 then (if l.2 then X else Xi)
    else (if l.2 then Y else Yi)) t) (pidn 378 9)

theorem relA_eq {X Xi Y Yi : Nat} (hX : Cn 378 9 X) (hXi : Cn 378 9 Xi) (hY : Cn 378 9 Y)
    (hYi : Cn 378 9 Yi) : ∀ v : List (Fin 2 × Bool),
    fi24RelA (unpack 378 9 X) (unpack 378 9 Xi) (unpack 378 9 Y) (unpack 378 9 Yi) v =
      unpack 378 9 (relK X Xi Y Yi v) ∧ Cn 378 9 (relK X Xi Y Yi v)
  | [] => ⟨(idK_sound pIdK).symm, pIdC⟩
  | l :: v => by
    obtain ⟨ih1, ih2⟩ := relA_eq hX hXi hY hYi v
    have hl : (if l.1.val = 0 then (if l.2 then unpack 378 9 X else unpack 378 9 Xi)
        else (if l.2 then unpack 378 9 Y else unpack 378 9 Yi)) =
        unpack 378 9 (if l.1.val = 0 then (if l.2 then X else Xi) else (if l.2 then Y else Yi)) ∧
        Cn 378 9 (if l.1.val = 0 then (if l.2 then X else Xi) else (if l.2 then Y else Yi)) := by
      split_ifs
      · exact ⟨rfl, hX⟩
      · exact ⟨rfl, hXi⟩
      · exact ⟨rfl, hY⟩
      · exact ⟨rfl, hYi⟩
    have e : fi24RelA (unpack 378 9 X) (unpack 378 9 Xi) (unpack 378 9 Y) (unpack 378 9 Yi)
        (l :: v) = compA 378 (if l.1.val = 0 then (if l.2 then unpack 378 9 X else unpack 378 9 Xi)
          else (if l.2 then unpack 378 9 Y else unpack 378 9 Yi))
          (fi24RelA (unpack 378 9 X) (unpack 378 9 Xi) (unpack 378 9 Y) (unpack 378 9 Yi) v) := rfl
    have e2 : relK X Xi Y Yi (l :: v) = pcomp 378 9 (mask 9)
        (if l.1.val = 0 then (if l.2 then X else Xi) else (if l.2 then Y else Yi))
        (relK X Xi Y Yi v) := rfl
    rw [e, e2, ih1, hl.1, compA_unpack hl.2 ih2]
    exact ⟨rfl, canonK_pcomp hl.2 ih2⟩

@[expose] noncomputable def ZK : Nat := pWordK fi24ShapeZ
@[expose] noncomputable def XK : Nat := pWordK fi24ShapeX
@[expose] noncomputable def YK : Nat := pWordK fi24ShapeY
@[expose] noncomputable def XIK : Nat := pinvS 378 9 (mask 9) XK
@[expose] noncomputable def YIK : Nat := pinvS 378 9 (mask 9) YK
@[expose] noncomputable def Z2K : Nat := pcomp 378 9 (mask 9) ZK ZK

theorem invX : invEqK 378 9 (mask 9) (378 * 9) XK XIK = true := by quickRfl
theorem invY : invEqK 378 9 (mask 9) (378 * 9) YK YIK = true := by quickRfl
theorem cnXI : canonK 378 9 (mask 9) (378 * 9) XIK = true := by quickRfl
theorem cnYI : canonK 378 9 (mask 9) (378 * 9) YIK = true := by quickRfl

theorem zOrd : Nat.beq (pcomp 378 9 (mask 9) ZK Z2K) (pidn 378 9) = true := by quickRfl
theorem zNe : (!Nat.beq ZK (pidn 378 9)) = true := by quickRfl
theorem zCent : fi24KdGenWords.all (fun w => Nat.beq (pcomp 378 9 (mask 9) (pWordK w) ZK)
    (pcomp 378 9 (mask 9) ZK (pWordK w))) = true := by quickRfl
theorem zInv : Nat.beq (pcomp 378 9 (mask 9) (Fi24PC.S 1) ZK) (pcomp 378 9 (mask 9) Z2K (Fi24PC.S 1)) =
    true := by quickRfl
theorem rels_ok : CFSG.LieType.Multipliers.U43.rels.all (fun v =>
    Nat.beq (relK XK XIK YK YIK v) (pidn 378 9) || Nat.beq (relK XK XIK YK YIK v) ZK ||
      Nat.beq (relK XK XIK YK YIK v) Z2K) = true := by quickRfl
theorem x_out : (!(Nat.beq XK (pidn 378 9) || Nat.beq XK ZK || Nat.beq XK Z2K)) = true := by
  quickRfl

theorem shapeP : fi24ShapeP = true := by
  have hZ : fi24PWordA fi24ShapeZ = unpack 378 9 ZK := (pWord_eq fi24ShapeZ).1
  have cZ : Cn 378 9 ZK := (pWord_eq fi24ShapeZ).2
  have hX : fi24PWordA fi24ShapeX = unpack 378 9 XK := (pWord_eq fi24ShapeX).1
  have cX : Cn 378 9 XK := (pWord_eq fi24ShapeX).2
  have hY : fi24PWordA fi24ShapeY = unpack 378 9 YK := (pWord_eq fi24ShapeY).1
  have cY : Cn 378 9 YK := (pWord_eq fi24ShapeY).2
  have iX := invEqK_sound invX
  have iY := invEqK_sound invY
  have cB : Cn 378 9 (Fi24PC.S 1) := (pCn' (j := 1) (by norm_num)).1
  have hI : idA 378 = unpack 378 9 (pidn 378 9) := (idK_sound pIdK).symm
  have hZ2 : compA 378 (unpack 378 9 ZK) (unpack 378 9 ZK) = unpack 378 9 Z2K := compA_unpack cZ cZ
  have cZ2 : Cn 378 9 Z2K := canonK_pcomp cZ cZ
  unfold fi24ShapeP
  simp only [hZ, hX, hY, pStrong (j := 1) (by norm_num), hI]
  rw [iX.1, iY.1, hZ2]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨iX.2, iY.2⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [compA_unpack cZ cZ2, eqA_unpack (canonK_pcomp cZ cZ2) pIdC]
    exact zOrd
  · rw [eqA_unpack cZ pIdC]
    exact zNe
  · have hc := zCent
    rw [List.all_eq_true] at hc ⊢
    intro w hw
    obtain ⟨w1, w2⟩ := pWord_eq w
    rw [w1, compA_unpack w2 cZ, compA_unpack cZ w2,
      eqA_unpack (canonK_pcomp w2 cZ) (canonK_pcomp cZ w2)]
    exact hc w hw
  · rw [compA_unpack cB cZ, compA_unpack cZ2 cB, eqA_unpack (canonK_pcomp cB cZ) (canonK_pcomp cZ2 cB)]
    exact zInv
  · have hr := rels_ok
    rw [List.all_eq_true] at hr ⊢
    intro v hv
    obtain ⟨r1, r2⟩ := relA_eq cX cnXI cY cnYI v
    rw [r1, eqA_unpack r2 pIdC, eqA_unpack r2 cZ, eqA_unpack r2 cZ2]
    exact hr v hv
  · rw [eqA_unpack cX pIdC, eqA_unpack cX cZ, eqA_unpack cX cZ2]
    exact x_out

theorem check : fi24ShapeCheck = true := by
  unfold fi24ShapeCheck
  rw [sift_of siftZ, sift_of siftX, sift_of siftY, shapeP]
  rfl

end CertificateChecks.KernelLC.Fi24Shape

end
