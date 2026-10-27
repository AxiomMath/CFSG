
module

public import Certificates.Kernel.SporSch.HN.StrongK
public import Certificates.Kernel.SporSch.HN.Seeds2106
public import CFSG.Certificates.Kernel.SporSch.HNF5ModSound
public import CFSG.Certificates.Kernel.SporSch.HNStrongGlue
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.SporSch.HNF5KronSound
import CFSG.Certificates.Kernel.PackSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNStrong

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.HNSchreier CertificateChecks.KernelSporSch

theorem entK {K : Nat} (hK : K < 133) : Canon5 (ss K) ∧
    (HNS.OP K = 0 → Canon5 (ss (HNS.L K)) → Canon5 (ss (HNS.R K)) →
      ∀ i < 133, vm5 (ss (HNS.R K)) (ss (HNS.L K) i) = ss K i) ∧
    (HNS.OP K = 1 → ∀ i < 133, ss (HNS.L K) i = ss K i) := by
  rcases (by omega : K < 13 ∨ (13 ≤ K ∧ K < 47) ∨ (47 ≤ K ∧ K < 57) ∨ (57 ≤ K ∧ K < 67) ∨
      (67 ≤ K ∧ K < 77) ∨ (77 ≤ K ∧ K < 87) ∨ (87 ≤ K ∧ K < 97) ∨ (97 ≤ K ∧ K < 107) ∨
      (107 ≤ K ∧ K < 117) ∨ (117 ≤ K ∧ K < 127) ∨ 127 ≤ K) with
    h | h | h | h | h | h | h | h | h | h | h
  · exact F5Kron.krBlk_sound blk0 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk1 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk2 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk3 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk4 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk5 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk6 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk7 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk8 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk9 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk10 (by omega) (by omega)

theorem canon (k : Nat) (hk : k < 133) : Canon5 (ss k) := (entK hk).1

theorem mulE {K l r : Nat} (hK : K < 133) (ho : HNS.OP K = 0) (hl : HNS.L K = l)
    (hr : HNS.R K = r) : ∀ i < 133, vm5 (ss r) (ss l i) = ss K i := by
  subst hl hr
  have hs := CFSG.KC.Pack.allN_spec specLt K hK
  rw [CFSG.KC.Pack.band_iff, Nat.blt_eq, Nat.blt_eq] at hs
  exact (entK hK).2.1 ho (canon _ hs.1) (canon _ hs.2)

theorem copyE {K l : Nat} (hK : K < 133) (ho : HNS.OP K = 1) (hl : HNS.L K = l) :
    ∀ i < 133, ss l i = ss K i := by
  subst hl
  exact (entK hK).2.2 ho

theorem mul_eq {K l r : Nat} (hl1 : l < 133) (hr1 : r < 133) (hK : K < 133) (ho : HNS.OP K = 0)
    (hl : HNS.L K = l) (hr : HNS.R K = r) :
    mulM 5 133 (rows5 (ss l)) (rows5 (ss r)) = rows5 (ss K) :=
  mulM5_sound (canon l hl1) (canon r hr1) (mulE hK ho hl hr)

theorem copy_eq {K l : Nat} (hK : K < 133) (ho : HNS.OP K = 1) (hl : HNS.L K = l) :
    rows5 (ss K) = rows5 (ss l) :=
  rows5_congr fun i hi => (copyE hK ho hl i hi).symm

theorem rowsA_eq : rowsA = rows5 (ss 0) := by
  rw [HNSeeds.rowsA_eq]
  exact rows5_congr fun i hi => (Nat.eq_of_beq_eq_true (allN_spec eqA i hi)).symm

theorem rowsB_eq : rowsB = rows5 (ss 1) := by
  rw [HNSeeds.rowsB_eq]
  exact rows5_congr fun i hi => (Nat.eq_of_beq_eq_true (allN_spec eqB i hi)).symm

theorem idM_eq : idM 133 = rows5 (ss 2) :=
  (beq_iff_eq.1 (eqId5_sound fun i hi => Nat.eq_of_beq_eq_true (allN_spec id2 i hi))).symm

@[expose] def RegOK (arr : Array (Array (Array Nat))) (reg : Nat → Nat) : Prop :=
  arr.size = 11 ∧ ∀ r < 11, arr[r]! = rows5 (ss (reg r))

@[expose] def regRun : List (Nat × Nat × Nat) → Nat → (Nat → Nat) → Nat → Nat
  | [], _, reg => reg
  | (_, _, c) :: rest, k, reg => regRun rest (k + 1) fun r => if r = c then k else reg r

@[expose] noncomputable def progB : List (Nat × Nat × Nat) → Nat → (Nat → Nat) → Bool
  | [], _, _ => true
  | (a, b, c) :: rest, k, reg => decide (a < 11) && decide (b < 11) && decide (c < 11) &&
      decide (k < 133) && decide (reg a < 133) && decide (reg b < 133) && HNS.OP k == 0 &&
      HNS.L k == reg a && HNS.R k == reg b && progB rest (k + 1) fun r => if r = c then k else reg r

theorem regOK_step {arr : Array (Array (Array Nat))} {reg : Nat → Nat} {a b c k : Nat}
    (h : RegOK arr reg) (ha : a < 11) (hb : b < 11) (hc : c < 11)
    (hm : mulM 5 133 (rows5 (ss (reg a))) (rows5 (ss (reg b))) = rows5 (ss k)) :
    RegOK (arr.set! c (mulM 5 133 arr[a]! arr[b]!)) (fun r => if r = c then k else reg r) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp [h1], fun r hr => ?_⟩
  rw [h2 a ha, h2 b hb, hm, Array.set!_eq_setIfInBounds,
    getElem!_pos _ r (by simp [h1]; omega)]
  by_cases e : r = c
  · subst e
    simp only [Array.getElem_setIfInBounds_self, if_pos]
  · simp only [if_neg e]
    rw [Array.getElem_setIfInBounds_ne (by omega) (Ne.symm e),
      ← getElem!_pos arr r (by omega), h2 r hr]

theorem regOK_prog : ∀ (prog : List (Nat × Nat × Nat)) (k : Nat) (arr : Array (Array (Array Nat)))
    (reg : Nat → Nat), RegOK arr reg → progB prog k reg = true →
    RegOK (progRegsM arr prog) (regRun prog k reg)
  | [], _, _, _, h, _ => h
  | (a, b, c) :: rest, k, arr, reg, h, hp => by
    simp only [progB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hk⟩, hra⟩, hrb⟩, ho⟩, hl⟩, hr⟩, hrest⟩ := hp
    exact regOK_prog rest (k + 1) _ _ (regOK_step h ha hb hc (mul_eq hra hrb hk ho hl hr)) hrest

@[expose] def reg0 (r : Nat) : Nat := if r = 1 then 0 else if r = 2 then 1 else 2

theorem initRegs_get (A B : Array (Array Nat)) (r : Nat) (hr : r < 11) :
    (initRegsM A B)[r]! = if r = 1 then A else if r = 2 then B else idM 133 := by
  interval_cases r <;> rfl

theorem regOK_init : RegOK (initRegsM rowsA rowsB) reg0 := by
  refine ⟨by simp [initRegsM], fun r hr => ?_⟩
  rw [initRegs_get _ _ r hr, reg0]
  by_cases h1 : r = 1
  · rw [if_pos h1, if_pos h1, rowsA_eq]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : r = 2
    · rw [if_pos h2, if_pos h2, rowsB_eq]
    · rw [if_neg h2, if_neg h2, idM_eq]

theorem prog_ok : progB Data.subgroupProgram 3 reg0 = true := by quickRfl

theorem regs_ok : RegOK (progRegsM (initRegsM rowsA rowsB) Data.subgroupProgram)
    (regRun Data.subgroupProgram 3 reg0) :=
  regOK_prog _ 3 _ _ regOK_init prog_ok

theorem reg1 : regRun Data.subgroupProgram 3 reg0 1 = 0 := by decide

theorem reg2 : regRun Data.subgroupProgram 3 reg0 2 = 12 := by decide

@[expose] def letK (l : Int) : Nat := if 0 < l then 12 + l.toNat else 29 + (-l).toNat

@[expose] noncomputable def F (j : Nat) : Array (Array Nat) := rows5 (ss (13 + j))

@[expose] noncomputable def FI (j : Nat) : Array (Array Nat) := rows5 (ss (30 + j))

@[expose] noncomputable def SA : Array (Array (Array Nat)) := Array.ofFn (n := 17) fun i => F i.val

@[expose] noncomputable def SIA : Array (Array (Array Nat)) := Array.ofFn (n := 17) fun i => FI i.val

theorem mletter_eq {l : Int} (h0 : l ≠ 0) (h17 : l.natAbs ≤ 17) :
    mletter SA SIA l = rows5 (ss (letK l)) := by
  rw [mletter, letK]
  by_cases hp : 0 < l
  · rw [if_pos hp, if_pos hp, SA, ofFn_getElem! (by omega), F]
    congr 2
    omega
  · rw [if_neg hp, if_neg hp, SIA, ofFn_getElem! (by omega), FI]
    congr 2
    omega

@[expose] noncomputable def chainB (w : List Int) (o : Nat) : Bool :=
  decide (1 ≤ w.length) && decide (o + w.length ≤ 133) &&
    w.all (fun l => l != 0 && decide (l.natAbs ≤ 17) && decide (letK l < 133)) &&
    HNS.OP o == 1 && HNS.L o == letK (w.getD (w.length - 1) 0) &&
    (List.range (w.length - 1)).all fun u => HNS.OP (o + u + 1) == 0 &&
      HNS.L (o + u + 1) == letK (w.getD (w.length - 2 - u) 0) && HNS.R (o + u + 1) == o + u

theorem mword_one (S Si : Array (Array (Array Nat))) (l : Int) :
    mword S Si [l] = mulM 5 133 (mletter S Si l) (idM 133) := rfl

theorem chain_eq {w : List Int} {o : Nat} (h : chainB w o = true) :
    mword SA SIA w = rows5 (ss (o + w.length - 1)) := by
  simp only [chainB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, hlen⟩, hl⟩, ho⟩, hL⟩, hs⟩ := h
  have hlet : ∀ t < w.length, mletter SA SIA (w.getD t 0) = rows5 (ss (letK (w.getD t 0))) ∧
      letK (w.getD t 0) < 133 := fun t ht => by
    have hm : w.getD t 0 ∈ w := by
      rw [List.getD_eq_getElem _ _ ht]
      exact List.getElem_mem ht
    obtain ⟨⟨a, b⟩, c⟩ := hl _ hm
    exact ⟨mletter_eq a b, c⟩
  have key : ∀ t, t < w.length → mword SA SIA (w.drop (w.length - 1 - t)) = rows5 (ss (o + t)) := by
    intro t
    induction t with
    | zero =>
      intro _
      have e : w.drop (w.length - 1 - 0) = [w.getD (w.length - 1) 0] := by
        rw [Nat.sub_zero, List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega),
          List.getD_eq_getElem _ _ (by omega)]
      rw [e, mword_one, (hlet _ (by omega)).1, mulM5_idR (canon _ (hlet _ (by omega)).2), Nat.add_zero,
        copy_eq (by omega) ho hL]
    | succ t ih =>
      intro ht
      obtain ⟨⟨a, b⟩, c⟩ := hs t (by omega)
      have e : w.drop (w.length - 1 - (t + 1)) =
          w.getD (w.length - 2 - t) 0 :: w.drop (w.length - 1 - t) := by
        rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem _ _ (by omega)]
        congr 2 <;> omega
      rw [e, mword, ih (by omega), (hlet _ (by omega)).1]
      rw [mul_eq (hlet _ (by omega)).2 (by omega) (by omega) a b c]
      rfl
  have := key (w.length - 1) (by omega)
  rwa [show w.length - 1 - (w.length - 1) = 0 by omega, List.drop_zero,
    show o + (w.length - 1) = o + w.length - 1 by omega] at this

@[expose] def offs : List Nat := [64, 66, 70, 76, 79, 84, 94, 97, 101, 105, 110, 113, 118, 125, 129]

@[expose] noncomputable def strongB : Bool :=
  LocalData.strongWords.size == 17 &&
  (List.range 17).all (fun j => HNS.OP (13 + j) == 1 && HNS.OP (47 + j) == 0 &&
    HNS.L (47 + j) == 13 + j && HNS.R (47 + j) == 30 + j) &&
  HNS.L 13 == 0 && HNS.L 14 == 12 &&
  (List.range 15).all fun u => chainB LocalData.strongWords[u + 2]! (offs.getD u 0) &&
    HNS.L (15 + u) == offs.getD u 0 + LocalData.strongWords[u + 2]!.length - 1 &&
    (LocalData.strongWords[u + 2]!).all fun l => decide (l.natAbs ≤ u + 2)

theorem strong_ok : strongB = true := by quickRfl

theorem strong_parts : LocalData.strongWords.size = 17 ∧
    (∀ j < 17, ((HNS.OP (13 + j) = 1 ∧ HNS.OP (47 + j) = 0) ∧ HNS.L (47 + j) = 13 + j) ∧
      HNS.R (47 + j) = 30 + j) ∧ HNS.L 13 = 0 ∧ HNS.L 14 = 12 ∧
    ∀ u < 15, (chainB LocalData.strongWords[u + 2]! (offs.getD u 0) = true ∧
      HNS.L (15 + u) = offs.getD u 0 + LocalData.strongWords[u + 2]!.length - 1) ∧
      ∀ l ∈ LocalData.strongWords[u + 2]!, decide (l.natAbs ≤ u + 2) = true := by
  have hs := strong_ok
  simp only [strongB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hs
  obtain ⟨⟨⟨⟨hsz, hj⟩, h13⟩, h14⟩, hw⟩ := hs
  exact ⟨hsz, hj, h13, h14, hw⟩

theorem inv_id {j : Nat} (hj : j < 17) : ∀ i < 133, vm5 (ss (30 + j)) (ss (13 + j) i) = idRow5 i := by
  intro i hi
  obtain ⟨⟨⟨-, a⟩, b⟩, c⟩ := strong_parts.2.1 j hj
  rw [mulE (by omega) a b c i hi]
  exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec ids j hj) i hi)

theorem F_inv {j : Nat} (hj : j < 17) : invM 5 133 (F j) = FI j :=
  invM5_eq (canon _ (by omega)) (canon _ (by omega)) (inv_id hj)

theorem F_mul_FI {j : Nat} (hj : j < 17) : (mulM 5 133 (F j) (FI j) == idM 133) = true := by
  obtain ⟨⟨⟨-, a⟩, b⟩, c⟩ := strong_parts.2.1 j hj
  rw [F, FI, mul_eq (by omega) (by omega) (by omega) a b c]
  exact eqId5_sound fun i hi => Nat.eq_of_beq_eq_true (allN_spec (allN_spec ids j hj) i hi)

theorem regs_12 : (progRegsM (initRegsM rowsA rowsB) Data.subgroupProgram)[1]! = F 0 ∧
    (progRegsM (initRegsM rowsA rowsB) Data.subgroupProgram)[2]! = F 1 := by
  obtain ⟨h1, h2'⟩ := regs_ok
  obtain ⟨-, hj, h13, h14, -⟩ := strong_parts
  refine ⟨?_, ?_⟩
  · rw [h2' 1 (by omega), reg1, F, copy_eq (by omega) (hj 0 (by omega)).1.1.1 h13]
  · rw [h2' 2 (by omega), reg2, F, copy_eq (by omega) (hj 1 (by omega)).1.1.1 h14]

theorem words_ok {j : Nat} (h2 : 2 ≤ j) (h17 : j < 17) :
    (∀ l ∈ LocalData.strongWords[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      mword SA SIA LocalData.strongWords[j]! = F j := by
  obtain ⟨-, hj, -, -, hw⟩ := strong_parts
  obtain ⟨u, rfl⟩ : ∃ u, j = u + 2 := ⟨j - 2, by omega⟩
  obtain ⟨⟨hc, hL⟩, hal⟩ := hw u (by omega)
  refine ⟨fun l hl => ?_, ?_⟩
  · have := of_decide_eq_true (hal l hl)
    have hc' := hc
    simp only [chainB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hc'
    exact ⟨(hc'.1.1.1.2 l hl).1.1, this⟩
  · have hL' : HNS.L (13 + (u + 2)) =
        offs.getD u 0 + LocalData.strongWords[u + 2]!.length - 1 := by
      rw [show 13 + (u + 2) = 15 + u by omega]
      exact hL
    change mword SA SIA _ = rows5 (ss (13 + (u + 2)))
    rw [chain_eq hc, copy_eq (by omega) (hj (u + 2) (by omega)).1.1.1 hL']

theorem strong_eq :
    extendStrongM #[(progRegsM (initRegsM rowsA rowsB) Data.subgroupProgram)[1]!,
      (progRegsM (initRegsM rowsA rowsB) Data.subgroupProgram)[2]!] LocalData.strongWords =
      (SA, SIA) := by
  refine extendStrongM_eq (s := 17) rfl strong_parts.1 (by omega) (fun j hj' => ?_)
    (fun j hj => F_inv hj) fun j h2 h17 => words_ok h2 h17
  interval_cases j
  · rw [getElem!_pos _ 0 (by simp), ← regs_12.1]
    rfl
  · rw [getElem!_pos _ 1 (by simp), ← regs_12.2]
    rfl

end CertificateChecks.KernelSporSch.HNStrong

end
