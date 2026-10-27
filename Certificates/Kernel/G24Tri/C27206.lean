module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24TriData
public import Certificates.Kernel.G24Tri.Chk27206
public import Certificates.Kernel.EvenSporG24.TblText
public import CFSG.Certificates.Kernel.G24TriSound
public import CFSG.Certificates.Kernel.LBindSound
public import Certificates.Kernel.Co1B.Tri2045Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24.Tri27206

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Co1BPair CFSG.KC.G24Tri
  CFSG.EvenSporadicStandard.G24Aut CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block
open CertificateChecks.KernelCo1B.Tri2045 (strong_facts)

theorem nums_eq (cs : List Char) (h : (cs.splitOn ' ').all goodP = true) :
    parseNums (String.ofList cs) = (numsOf cs).toArray :=
  CertificateChecks.EvenSporG24.parseNums_ofList cs h

theorem tri_eq : triNums = (numsOf TT.chars).toArray := by
  have h : triNums = parseNums triText := rfl
  rw [h, TT.eq]
  exact nums_eq _ kGoodT

theorem la_eq : laNums = (numsOf LT.chars).toArray := by
  have h : laNums = parseNums laText := rfl
  rw [h, LT.eq]
  exact nums_eq _ kGoodL

theorem bindT {i : Nat} (hi : i < 3) :
    lbindK ((numsOf TT.chars).extract (i * 2731 + 1) (i * 2731 + 1366)) 1365 11 (PK (2 * i)) =
        true ∧
      lbindK ((numsOf TT.chars).extract (i * 2731 + 1366) (i * 2731 + 2731)) 1365 11
        (PK (2 * i + 1)) = true := by
  have h := List.all_eq_true.1 kBindT i (List.mem_range.2 hi)
  rwa [Bool.and_eq_true] at h

theorem triA_eq {i : Nat} (hi : i < 3) : triA i = unpack 1365 11 (PK (2 * i)) := by
  unfold triA
  rw [tri_eq, List.extract_toArray]
  exact lbindK_sound (bindT hi).1

theorem triB_eq {i : Nat} (hi : i < 3) : triB i = unpack 1365 11 (PK (2 * i + 1)) := by
  unfold triB
  rw [tri_eq, List.extract_toArray]
  exact lbindK_sound (bindT hi).2

theorem triM_eq {i : Nat} (hi : i < 3) : triM i = mT i := by
  have h := List.all_eq_true.1 kM i (List.mem_range.2 hi)
  unfold triM
  rw [tri_eq]
  exact Nat.eq_of_beq_eq_true h

theorem bindL : lbindK ((numsOf LT.chars).extract 0 1365) 1365 11 (PK 6) = true ∧
    lbindK ((numsOf LT.chars).extract 17743 19108) 1365 11 (PK 7) = true := by
  have h := kBindL
  rwa [Bool.and_eq_true] at h

theorem tA_eq : tAa = unpack 1365 11 (sP 0) := by
  unfold tAa
  rw [la_eq, List.extract_toArray]
  exact lbindK_sound bindL.1

theorem oa_eq : oa = unpack 1365 11 (sP 2) := by
  unfold oa
  rw [la_eq, List.extract_toArray]
  exact lbindK_sound bindL.2

theorem xa_eq : xa = unpack 1365 11 (sP 1) := by
  have h : xa = twoBStrong[0]! := rfl
  rw [h, strong_facts.2 0 (by norm_num),
    Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec kSR 0 (by norm_num))]
  rfl

theorem hb : Binds 1365 11 LC.S 6 3 LC.BP twoBStrong twoBChainBase.toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, strong_facts.1, fun j hj => ?_,
    by simp [twoBChainBase], fun t ht => ?_⟩
  · rw [strong_facts.2 j hj, Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec kSR j hj)]
  · rw [Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec kB t ht)]
    interval_cases t <;> rfl

theorem inD_of {k : Nat} (hk : k < 6) : inD (unpack 1365 11 (PK k)) = true := by
  unfold inD twoBLevels
  exact siftK_sound hb kP LC.hl rfl
    (range_of_canonK (CFSG.KC.Pack.allN_spec kCan k (by omega)))
    (CFSG.KC.Pack.allN_spec kSift k hk)

theorem eqA_self (t : Array Nat) : eqA nn t t = true := CertificateChecks.KernelCo1B.Tri2045.eqA_refl _ _

theorem tri_of {i : Nat} (hi : i < 3) {s : Array Nat} (hs : s = unpack 1365 11 (sP i)) :
    triCheck s i = true := by
  have hid := CertificateChecks.KernelCo1B.Tri2045.idA_eq
  have cA := CFSG.KC.Pack.allN_spec kCan (2 * i) (by omega)
  have cB := CFSG.KC.Pack.allN_spec kCan (2 * i + 1) (by omega)
  have hc := CFSG.KC.Pack.allN_spec kComm i hi
  have ho := CFSG.KC.Pack.allN_spec kOrd i hi
  simp only [Bool.and_eq_true] at hc ho
  obtain ⟨⟨cS, eA⟩, eB⟩ := hc
  obtain ⟨⟨oA, oB⟩, oC⟩ := ho
  have iA := (invEqK_sound (CFSG.KC.Pack.allN_spec kInv (2 * i) (by omega))).2
  have iB := (invEqK_sound (CFSG.KC.Pack.allN_spec kInv (2 * i + 1) (by omega))).2
  rw [← (invEqK_sound (CFSG.KC.Pack.allN_spec kInv (2 * i) (by omega))).1] at iA
  rw [← (invEqK_sound (CFSG.KC.Pack.allN_spec kInv (2 * i + 1) (by omega))).1] at iB
  have hm : (triM i == 5 || triM i == 7) = true := by
    rw [triM_eq hi]
    interval_cases i <;> rfl
  have hmp : 0 < triM i := by
    rw [triM_eq hi]
    interval_cases i <;> norm_num [mT]
  unfold triCheck
  rw [triA_eq hi, triB_eq hi, hs, inD_of (by omega), inD_of (by omega), iA, iB,
    CFSG.KC.BfsPin.compA_unpack cA cS, CFSG.KC.BfsPin.compA_unpack cS cA, Nat.eq_of_beq_eq_true eA,
    CFSG.KC.BfsPin.compA_unpack cB cS, CFSG.KC.BfsPin.compA_unpack cS cB, Nat.eq_of_beq_eq_true eB,
    eqA_self, eqA_self, ordIs_of (v := 2) hid cA (by norm_num) oA,
    ordIs_of (v := 3) hid cB (by norm_num) oB, hm, CFSG.KC.BfsPin.compA_unpack cA cB,
    ordIs_of (v := triM i) hid (CFSG.KC.BfsPin.canonK_pcomp cA cB) hmp
      (by rw [triM_eq hi]; exact oC)]
  rfl

theorem triangles_ok : trianglesOK = true := by
  unfold trianglesOK
  rw [tri_of (by norm_num) tA_eq, tri_of (by norm_num) xa_eq, tri_of (by norm_num) oa_eq]
  rfl

end CertificateChecks.KernelG24.Tri27206

end
