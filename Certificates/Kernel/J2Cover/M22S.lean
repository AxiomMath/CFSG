module

public import Certificates.Kernel.J2Cover.M22Dec
public import Certificates.Kernel.J2Cover.K20A
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Child3 CFSG.KC.J2Models CFSG.KC.J2Cover
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models
open CFSG.Monster.B.Co2 (allLt_iff)

theorem nth_getD {α : Type} (d : α) : ∀ (l : List α) (k : Nat), nth d l k = l.getD k d
  | [], _ => by simp [nth]
  | _ :: _, 0 => rfl
  | _ :: l, k + 1 => by
    rw [List.getD_cons_succ]
    exact nth_getD d l k

theorem wordP_foldr : ∀ w : List Nat,
    wordP w = w.foldr (fun x acc => pcomp 315 9 (mask 9) (letP x) acc) (pidn 315 9)
  | [] => rfl
  | k :: w => by
    rw [List.foldr_cons, ← wordP_foldr w]
    rfl

theorem kS1 : allN 3 (fun k => allN 128 fun b => bAnd(Nat.blt (lmul k b) 128,
    Nat.beq (ELT (lmul k b)) (pcomp 315 9 (mask 9) (YT k) (ELT b)))) = true := by quickRfl

theorem kS2 : allN 128 (fun a => allN 128 fun b =>
    bIf(Nat.beq a b, true, bIf(Nat.beq (ELT a) (ELT b), false, true))) = true := by quickRfl

theorem kS3 : allN 128 (fun a => bAnd(Nat.blt (invIdx a) 128, Nat.beq (mtK a (invIdx a)) 0)) =
    true := by quickRfl

theorem sC : sCheck = true := by
  have p1 : allLt 3 (fun k => allLt 128 fun b =>
      decide (lmul k b < 128) && eqA 315 eltArrs[lmul k b]! (compA 315 yArrs[k]! eltArrs[b]!)) =
      true := by
    refine allLt_iff.2 fun k hk => allLt_iff.2 fun b hb => ?_
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec kS1 k hk) b hb)
    have hl : lmul k b < 128 := Nat.le_of_ble_eq_true h1
    have cy := allN_spec kYc k hk
    rw [eltArrs_eq _ hl, yArrs_eq k hk, eltArrs_eq b hb, compA_unpackN cy (eltT_canon b hb),
      eqA_unpackN (eltT_canon _ hl) (canon_pcN cy (eltT_canon b hb)), h2]
    simp [hl]
  have p2 : allLt 128 (fun a => allLt 128 fun b => a == b || !(eqA 315 eltArrs[a]! eltArrs[b]!)) =
      true := by
    refine allLt_iff.2 fun a ha => allLt_iff.2 fun b hb => ?_
    have h := allN_spec (allN_spec kS2 a ha) b hb
    rw [eltArrs_eq a ha, eltArrs_eq b hb, eqA_unpackN (eltT_canon a ha) (eltT_canon b hb)]
    by_cases e : a = b
    · simp [e]
    · have hf : Nat.beq a b = false := Bool.eq_false_iff.2 fun h' => e (Nat.eq_of_beq_eq_true h')
      rw [hf] at h
      cases hE : Nat.beq (ELT a) (ELT b)
      · simp
      · rw [hE] at h
        exact absurd h Bool.false_ne_true
  have p3 : allLt 128 (fun a => decide (invIdx a < 128) && (mulTab[a]!)[invIdx a]! == 0) = true := by
    refine allLt_iff.2 fun a ha => ?_
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec kS3 a ha)
    have hl : invIdx a < 128 := Nat.le_of_ble_eq_true h1
    rw [mt_pt, Nat.eq_of_beq_eq_true h2]
    simp [hl]
  unfold sCheck
  rw [p1, p2, p3]
  rfl

@[expose] noncomputable def fCS (i : Nat) : Bool :=
  allN 2 fun j => bAnd(Nat.blt (actK j i) 4725, bAnd(Nat.blt (witK j i) 128,
    Nat.beq (pcomp 315 9 (mask 9) (RPT i) (letP j))
      (pcomp 315 9 (mask 9) (ELT (witK j i)) (RPT (actK j i)))))

#lc_blocks CSB fCS 4725 32

theorem cs_facts (i : Nat) (hi : i < 4725) (j : Nat) (hj : j < 2) : actK j i < 4725 ∧
    witK j i < 128 ∧ pcomp 315 9 (mask 9) (RPT i) (letP j) =
      pcomp 315 9 (mask 9) (ELT (witK j i)) (RPT (actK j i)) := by
  have h := allN_spec (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) CSB.all i hi) j hj
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem csC : cosetCheck = true := by
  unfold cosetCheck
  refine allLt_iff.2 fun i hi => allLt_iff.2 fun j hj => ?_
  obtain ⟨h1, h2, h3⟩ := cs_facts i hi j hj
  rw [act_pt, wit_pt, repArrs_eq i hi, letter_eq, eltArrs_eq _ h2, repArrs_eq _ h1,
    compA_unpackN (repT_canon i hi) (letP_canon j), compA_unpackN (eltT_canon _ h2) (repT_canon _ h1),
    eqA_unpackN (canon_pcN (repT_canon i hi) (letP_canon j))
      (canon_pcN (eltT_canon _ h2) (repT_canon _ h1)), h3, Nat.beq_refl]
  simp [h1, h2]

@[expose] noncomputable def fMM (a : Nat) : Bool :=
  allN 128 fun b => bAnd(Nat.blt (mtK a b) 128,
    Nat.beq (ELT (mtK a b)) (pcomp 315 9 (mask 9) (ELT a) (ELT b)))

#lc_blocks MMB fMM 128 4

theorem kE0 : Nat.beq (ELT 0) (pidn 315 9) = true := by quickRfl

theorem kT : allN 128 (fun a => bIf(Nat.beq a 0, true,
    Nat.beq (ELT a) (pcomp 315 9 (mask 9) (YT (gen a)) (ELT (par a))))) = true := by quickRfl

theorem kYW : allN 3 (fun k => allL (fun x => Nat.blt x 2) (nth [] yWords k)) = true := by quickRfl

theorem yFold_pt (k : Nat) (hk : k < 3) (i : Nat) (hi : i < 4725) : yDK k i =
    (yWords.getD k []).foldl (fun pc x => (mtK pc.1 (witK x pc.2), actK x pc.2)) (0, i) := by
  rw [← yDecomp_pt k i hk hi, ← nth_getD]
  unfold yDecomp
  simp only [mt_pt, wit_pt, act_pt]

theorem dec_facts : ∀ i < 4725, ∀ a < 128, pg 7 (mask 7) (DP a) i < 128 ∧
    pg 13 (mask 13) (DI a) i < 4725 ∧ pcomp 315 9 (mask 9) (RPT i) (ELT a) =
      pcomp 315 9 (mask 9) (ELT (pg 7 (mask 7) (DP a) i)) (RPT (pg 13 (mask 13) (DI a) i)) := by
  refine decomp_sound (RP := RPT) (EL := ELT) (LP := letP) (YT := YT) (mt := mtK) (wit := witK)
    (act := actK) (yw := yWords) (gn' := gen) (pr' := par) (yD := yDK)
    (P := fun a i => pg 7 (mask 7) (DP a) i) (I := fun a i => pg 13 (mask 13) (DI a) i)
    repT_canon eltT_canon (fun j _ => letP_canon j) (Nat.eq_of_beq_eq_true kE0)
    (fun a ha h1 => ?_) (fun k hk => ?_) (fun a ha b hb => ?_) (fun i hi j hj => cs_facts i hi j hj)
    yFold_pt (fun i hi => (dc_rest 0 (by omega)).1 rfl i hi)
    (fun a ha h1 i hi => (((dc_rest a ha).2 (by omega)).2 i hi).2)
  · have h := allN_spec kT a ha
    rw [beq_false (by omega)] at h
    exact ⟨((dc_rest a ha).2 (by omega)).1, gen_lt a, Nat.eq_of_beq_eq_true h⟩
  · rw [← nth_getD, ← wordP_foldr, Nat.eq_of_beq_eq_true (allN_spec kY k hk)]
    exact ⟨fun x hx => Nat.le_of_ble_eq_true (allL_spec (allN_spec kYW k hk) x hx), rfl⟩
  · have h := allN_spec (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) MMB.all a ha) b hb
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    exact ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem sdC : sDecompCheck = true := by
  unfold sDecompCheck
  refine allLt_iff.2 fun i hi => allLt_iff.2 fun a ha => ?_
  obtain ⟨h1, h2, h3⟩ := dec_facts i hi a ha
  have ep : pTab i a = pg 7 (mask 7) (DP a) i := by
    rw [pT_pt]
    unfold pK
    rw [blt_true ha]
  have ei : iTab i a = pg 13 (mask 13) (DI a) i := by
    rw [iT_pt]
    unfold iK
    rw [blt_true ha]
  rw [ep, ei, repArrs_eq i hi, eltArrs_eq a ha, eltArrs_eq _ h1, repArrs_eq _ h2,
    compA_unpackN (repT_canon i hi) (eltT_canon a ha), compA_unpackN (eltT_canon _ h1) (repT_canon _ h2),
    eqA_unpackN (canon_pcN (repT_canon i hi) (eltT_canon a ha))
      (canon_pcN (eltT_canon _ h1) (repT_canon _ h2)), h3, Nat.beq_refl]
  simp [h1, h2]

end CertificateChecks.KernelJ2Cover

end
