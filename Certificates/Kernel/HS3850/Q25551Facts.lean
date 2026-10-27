module

public import Certificates.Kernel.HS3850.Q25551S
public import Certificates.Kernel.HS3850.Facts25371

public section

set_option maxRecDepth 400000

#kqb_all CFSG.KD.HS3850.EQ CFSG.KD.HS3850.ckQ 240

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KC.PkPow
open CFSG.KD.LQT.C4126 CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.TwoHS
open CFSG.KD.LQT.HO (Cn cIdn)

theorem ok25551_parts : Nat.beq (wfoldR (fun _ => q1A) (List.replicate 5 0)) idn = true ∧
    Nat.beq (wfoldR (fun _ => q1B) (List.replicate 5 0)) idn = true ∧
    Nat.beq (wfoldR (fun _ => pc q1A q1B) (List.replicate 10 0)) (HC.F 5) = true := by
  have h := ok25551
  simp only [CFSG.KS.PEnum.strictB_app', bAnd_iff] at h
  exact h

theorem tabA_eq : hsOdd1TabA = unpack 3850 12 q1A ∧ Cn q1A := by
  unfold hsOdd1TabA
  exact c1Word (by decide)

theorem tabB_eq : hsOdd1TabB = unpack 3850 12 q1B ∧ Cn q1B := by
  unfold hsOdd1TabB
  exact c1Word (by decide)

theorem powA_true : hsOdd1PowA = true := by
  obtain ⟨ha, ca⟩ := tabA_eq
  have w := wordTabS_unp (gs := #[hsOdd1TabA]) (L := fun _ => q1A) (List.replicate 5 0)
    (fun l hl => by
      rw [List.eq_of_mem_replicate hl]
      exact ⟨by rw [ha]; rfl, ca⟩)
  unfold hsOdd1PowA
  rw [w.1, idTab_idn, beq_pc' w.2 cIdn]
  exact ok25551_parts.1

theorem powB_true : hsOdd1PowB = true := by
  obtain ⟨hb, cb⟩ := tabB_eq
  have w := wordTabS_unp (gs := #[hsOdd1TabB]) (L := fun _ => q1B) (List.replicate 5 0)
    (fun l hl => by
      rw [List.eq_of_mem_replicate hl]
      exact ⟨by rw [hb]; rfl, cb⟩)
  unfold hsOdd1PowB
  rw [w.1, idTab_idn, beq_pc' w.2 cIdn]
  exact ok25551_parts.2.1

theorem powAB_true : hsOdd1PowAB = true := by
  obtain ⟨ha, ca⟩ := tabA_eq
  obtain ⟨hb, cb⟩ := tabB_eq
  have e : hsOdd1TabAB = unpack 3850 12 (pc q1A q1B) := by
    unfold hsOdd1TabAB
    rw [ha, hb, comp_pc' ca cb]
  have w := wordTabS_unp (gs := #[hsOdd1TabAB]) (L := fun _ => pc q1A q1B) (List.replicate 10 0)
    (fun l hl => by
      rw [List.eq_of_mem_replicate hl]
      exact ⟨by rw [e]; rfl, cn_pc ca cb⟩)
  unfold hsOdd1PowAB
  rw [w.1, (cent_parts (k := 5) (by norm_num)).1, beq_pc' w.2 (cent_parts (k := 5) (by norm_num)).2]
  exact ok25551_parts.2.2

theorem cmK_of_ptc {X G : Nat} (hX : Cn X) (hG : Cn G) (h : ptc X G = false) : cmK X G = false := by
  unfold ptc at h
  unfold cmK
  cases e : Nat.beq (pc X G) (pc G X)
  · rfl
  · have h1 : img (pc X G) 0 = img X (img G 0) := img_pc' hX (by norm_num)
    have h2 : img (pc G X) 0 = img G (img X 0) := img_pc' hG (by norm_num)
    rw [← h1, ← h2, Nat.eq_of_beq_eq_true e, Nat.beq_refl] at h
    exact absurd h (by decide)

theorem cmK_of_ptc2 {W X G : Nat} (hW : Cn W) (hX : Cn X) (hG : Cn G) (h : ptc2 W X G = false) :
    cmK (pc W X) G = false := by
  unfold ptc2 at h
  unfold cmK
  cases e : Nat.beq (pc (pc W X) G) (pc G (pc W X))
  · rfl
  · have h1 : img (pc (pc W X) G) 0 = img W (img X (img G 0)) := by
      rw [img_pc' (cn_pc hW hX) (by norm_num), img_pc' hW (pg_lt hG (by norm_num))]
    have h2 : img (pc G (pc W X)) 0 = img G (img W (img X 0)) := by
      rw [img_pc' hG (by norm_num), img_pc' hW (by norm_num)]
    rw [← h1, ← h2, Nat.eq_of_beq_eq_true e, Nat.beq_refl] at h
    exact absurd h (by decide)

theorem half_of : ∀ p0 p1 c0 c1 s : Bool, (p0 = false → c0 = false) → (p1 = false → c1 = false) →
    bIf(bAnd(p0, p1), bIf(bAnd(c0, c1), s, true), true) = true → (!(c0 && c1) || s) = true := by
  decide

theorem quart_of {W G0 G1 X : Nat} (hW : Cn W) (h0 : Cn G0) (h1 : Cn G1) (hX : Cn X)
    (h : qF W G0 G1 X = true) :
    ((!(cmK X G0 && cmK X G1) || sqK (pc X X)) &&
      (!(cmK (pc W X) G0 && cmK (pc W X) G1) || sqK (pc (pc W X) (pc W X)))) = true := by
  unfold qF at h
  rw [CFSG.KS.PEnum.strictB_app'] at h
  obtain ⟨ha, hb⟩ := (bAnd_iff _ _).1 h
  rw [Bool.and_eq_true]
  exact ⟨half_of _ _ _ _ _ (cmK_of_ptc hX h0) (cmK_of_ptc hX h1) ha,
    half_of _ _ _ _ _ (cmK_of_ptc2 hW hX h0) (cmK_of_ptc2 hW hX h1) hb⟩

theorem ptQ25551_of {i : Nat} (hi : i < 7680) : ptQ25551 i = true := by
  have hs : i / 32 < 240 := by omega
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (EQ.all (i / 32) hs) (i % 32) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.mul (i / 32) 32) (i % 32) = i := by
    change i / 32 * 32 + i % 32 = i
    omega
  rw [CFSG.KS.PEnum.strictB_app', e] at h
  have hb : Nat.blt i 7680 = true := Nat.blt_eq.mpr hi
  rw [hb] at h
  exact h

theorem quart_true : hsOdd1Quart = true := by
  obtain ⟨ha, ca⟩ := tabA_eq
  obtain ⟨hb, cb⟩ := tabB_eq
  have hgs : hsOdd1Tabs = #[unpack 3850 12 q1A, unpack 3850 12 q1B] := by
    unfold hsOdd1Tabs
    rw [ha, hb]
  have hW : Cn (FT.F 0) := ok_parts.1
  unfold hsOdd1Quart quartCheck
  rw [c1Enum_eq, facts_eq (k := 0) (by norm_num)]
  unfold penumRec
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < CFSG.KD.LQT.HN.A.cnt := by simpa using hi
  simp only [Array.getElem_ofFn]
  have hX := canonA hi'
  have hq := ptQ25551_of (cnt_A ▸ hi')
  unfold ptQ25551 at hq
  rw [CFSG.KS.PEnum.strictB_app'] at hq
  unfold quartPt quartPt2
  rw [all_two hgs, all_two hgs, commPt_eq hX ca, commPt_eq hX cb, commPt2_eq hW hX ca,
    commPt2_eq hW hX cb, comp_pc' hX hX, sqPt_eq (cn_pc hX hX), comp_pc' hW hX,
    comp_pc' (cn_pc hW hX) (cn_pc hW hX), sqPt_eq (cn_pc (cn_pc hW hX) (cn_pc hW hX))]
  exact quart_of hW ca cb hX hq

end CFSG.KD.HS3850

end
