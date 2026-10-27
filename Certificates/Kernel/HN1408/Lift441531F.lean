module

public import Certificates.Kernel.HN1408.Lift441531
public import Certificates.Kernel.HN1408.TableIGlue

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Lift

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.Blk CFSG.KD.HN1408
open CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel27
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native

theorem base : Cn UK ∧ Cn VK ∧ Cn ZK ∧ commP UK ZK = true ∧ commP VK ZK = true ∧
    canonK 5 4 (mask 4) (5 * 4) LU = true ∧ canonK 5 4 (mask 4) (5 * 4) LV = true ∧
    blkMapK 1408 11 4 (TB.F 0) 5 UK LU = true ∧ blkMapK 1408 11 4 (TB.F 0) 5 VK LV = true := by
  simpa only [bAnd_iff] using base_ok

theorem hU : tabW HaradaModel27.uWord = tabT (unpack 1408 11 UK) := (tabW_eq (by decide)).1
theorem hV : tabW HaradaModel27.vWord = tabT (unpack 1408 11 VK) := (tabW_eq (by decide)).1
theorem hZ : tabW wordZ = tabT (unpack 1408 11 ZK) := (tabW_eq (by decide)).1

theorem hlu : labU = tabT (unpack 5 4 LU) := by decide +kernel
theorem hlv : labV = tabT (unpack 5 4 LV) := by decide +kernel

theorem hcnt : TI1.cnt = 256 := (headI_spec kH1).2.2.1

theorem hT {i : Nat} (hi : i < 256) : Cn (TI1.T i) := r1.2.2 i (by rw [hcnt]; exact hi)

theorem compT_pc {X Y : Nat} (hX : Cn X) (hY : Cn Y) :
    compT 1408 (tabT (unpack 1408 11 X)) (tabT (unpack 1408 11 Y)) = tabT (unpack 1408 11 (pc X Y)) :=
  compT_unpack hX hY

theorem cn_pc {X Y : Nat} (hX : Cn X) (hY : Cn Y) : Cn (pc X Y) := canonK_pcomp hX hY

theorem sqZ_eq {X : Nat} (hX : Cn X) :
    sqZ (tabT (unpack 1408 11 X)) (tabT (unpack 1408 11 ZK)) = sqZK X := by
  unfold sqZ sqZK
  rw [compT_pc hX hX, idT_eq, tblEq_eq (cn_pc hX hX) cId, tblEq_eq (cn_pc hX hX) base.2.2.1]

theorem commZ_eq {X Y : Nat} (hX : Cn X) (hY : Cn Y) :
    commZ (tabT (unpack 1408 11 X)) (tabT (unpack 1408 11 Y)) (tabT (unpack 1408 11 ZK)) =
      commZK X Y := by
  unfold commZ commZK
  rw [compT_pc hX hY, compT_pc hY hX, compT_pc base.2.2.1 (cn_pc hY hX),
    tblEq_eq (cn_pc hX hY) (cn_pc hY hX), tblEq_eq (cn_pc hX hY) (cn_pc base.2.2.1 (cn_pc hY hX))]

theorem all_eq {f : Table → Bool} {g : Nat → Bool}
    (hfg : ∀ i < 256, f (tabT (unpack 1408 11 (TI1.T i))) = g i) :
    (hRec 1408 11 TI1.cnt TI1.T TI1.PL).1.all f = allN 256 g := by
  have hx : ∀ i (hi : i < (hRec 1408 11 TI1.cnt TI1.T TI1.PL).1.size),
      (hRec 1408 11 TI1.cnt TI1.T TI1.PL).1[i] = tabT (unpack 1408 11 (TI1.T i)) := by
    intro i hi
    simp [hRec]
  have hs : (hRec 1408 11 TI1.cnt TI1.T TI1.PL).1.size = 256 := by rw [hRec_size, hcnt]
  apply Bool.eq_iff_iff.2
  rw [Array.all_eq_true, allN_iff']
  constructor
  · intro h i hi
    rw [← hfg i hi, ← hx i (by rw [hs]; exact hi)]
    exact h i (by rw [hs]; exact hi)
  · intro h i hi
    rw [hx i hi, hfg i (by rw [← hs]; exact hi)]
    exact h i (by rw [← hs]; exact hi)

theorem facts441531 : liftOK = true := by
  obtain ⟨cU, cV, -, hUZ, hVZ, cLU, cLV, bU, bV⟩ := base
  unfold liftOK
  simp only [Bool.and_eq_true]
  rw [hU, hV, hZ, r1.2.1, hlu, hlv, blk1]
  refine ⟨⟨⟨⟨⟨⟨by decide, by decide⟩, ?_⟩, ?_⟩, blkMapOK_of cU cLU bU⟩, blkMapOK_of cV cLV bV⟩, ?_⟩
  · rw [commTT_eq cU base.2.2.1]
    exact hUZ
  · rw [commTT_eq cV base.2.2.1]
    exact hVZ
  · have hl := lift_ok
    unfold liftK at hl
    refine (all_eq (fun i hi => ?_)).trans hl
    rw [compT_pc cU (hT hi), sqZ_eq (cn_pc cU (hT hi))]
    refine congrArg (fun b => (!sqZK (pc UK (TI1.T i)) || b)) (all_eq (fun j hj => ?_))
    rw [compT_pc cV (hT hj), sqZ_eq (cn_pc cV (hT hj)),
      commZ_eq (cn_pc cU (hT hi)) (cn_pc cV (hT hj))]

end CFSG.KD.HN1408.Lift

end
