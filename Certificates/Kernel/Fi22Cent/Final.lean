module

public import Certificates.Kernel.Fi22Cent.Facts
public import Certificates.Kernel.Fi22Core.Chain
public import Certificates.Kernel.T46K.Chain
public import Certificates.Data.Kernel.Fi22.CentChecks
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PChainSound
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelFi22Cent.rsAll CertificateChecks.KernelFi22Cent.rs 6
#kon_join CertificateChecks.KernelFi22Cent.lvSlAll CertificateChecks.KernelFi22Cent.lvSl 30

namespace CertificateChecks.KernelFi22Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Fi22Cent CFSG.KS.Fi22L CFSG.KS.TW CFSG.KS.PC CFSG.KS.T46K
  CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CertificateChecks.KernelFi22C
  CertificateChecks.KernelT46

attribute [local irreducible] phiData CFSG.F4.Native.uPts

theorem uF_lt : ∀ f k y, y < 3510 → uF f k y < 3510
  | 0, _, y, hy => hy
  | f + 1, k, y, hy => by
    rw [uF_succ]
    split_ifs
    · exact hy
    · exact gA_lt (uF_lt f _ y hy)
    · exact (beta_get (uF_lt f _ y hy)).2

theorem uInvF_lt : ∀ f k x, x < 3510 → uInvF f k x < 3510
  | 0, _, x, hx => hx
  | f + 1, k, x, hx => by
    rw [uInvF_succ]
    split_ifs
    · exact hx
    · exact uInvF_lt f _ _ (gA_lt hx)
    · exact uInvF_lt f _ _ (bi_get hx).2

theorem cK_lt (k : Nat) {x : Nat} (hx : x < 3510) : cK k x < 3510 := by
  unfold cK
  rw [TW.strictN_eq']
  exact uF_lt _ _ _ (gA_lt (uInvF_lt _ _ _ hx))

theorem ap_idT {x : Nat} (hx : x < 3510) : ap (idT 3510) x = x := by
  unfold idT
  rw [CFSG.Sporadic.Th.ap_ofFn _ hx, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem wordTab_eq (w : List Nat) (hw : ∀ k ∈ w, k < 3510) {x : Nat} (hx : x < 3510) :
    ap (wordTab orbL (genTables orbL (-2)) w) x = wordK w x ∧ wordK w x < 3510 := by
  induction w with
  | nil => exact ⟨ap_idT hx, hx⟩
  | cons k w ih =>
    obtain ⟨h1, h2⟩ := ih fun k' hk' => hw k' (List.mem_cons_of_mem k hk')
    have hk := hw k List.mem_cons_self
    change ap (compT 3510 (cTab orbL (genTables orbL (-2)) k)
      (wordTab orbL (genTables orbL (-2)) w)) x = cK k (wordK w x) ∧ cK k (wordK w x) < 3510
    rw [ap_compT _ _ hx, h1, cTab_eq hk h2]
    exact ⟨rfl, cK_lt k h2⟩

theorem iterN_itK {f g : Nat → Nat} (hfg : ∀ y < 3510, f y = g y) (hg : ∀ y < 3510, g y < 3510) :
    ∀ m x, x < 3510 → iterN f m x = itK g m x
  | 0, _, _ => rfl
  | m + 1, x, hx => by
    change iterN f m (f x) = strictN (g x) (fun x => itK g m x)
    rw [TW.strictN_eq', hfg x hx]
    exact iterN_itK hfg hg m _ (hg x hx)

theorem chainQ_toList : chainQ.toList = QL := rfl

theorem pow_ok {w : List Nat} {m : Nat} (hw : ∀ k ∈ w, k < 3510) (h : powK w m QL = true) :
    cPowOK orbL w m = true := by
  unfold cPowOK
  rw [← Array.all_toList, chainQ_toList, List.all_eq_true]
  have hQ : ∀ q ∈ QL, q < 3510 := by decide
  have key : ∀ (Q : List Nat), (∀ q ∈ Q, q < 3510) → powK w m Q = true →
      ∀ q ∈ Q, (iterN (ap (wordTab orbL (genTables orbL (-2)) w)) m q == ap orbL.alpha q) = true := by
    intro Q
    induction Q with
    | nil => intro _ _ q hq; exact absurd hq List.not_mem_nil
    | cons q Q ih =>
      intro hQ h r hr
      change Bool.rec (motive := fun _ => Bool) false (powK w m Q)
        (Nat.beq (itK (wordK w) m q) (gA q)) = true at h
      rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
      rcases List.mem_cons.1 hr with rfl | hr
      · have hr3 := hQ r List.mem_cons_self
        rw [beq_iff_eq, iterN_itK (fun y hy => (wordTab_eq w hw hy).1)
          (fun y hy => (wordTab_eq w hw hy).2) m r hr3, h.1, gA_eq hr3]
      · exact ih (fun q hq => hQ q (List.mem_cons_of_mem _ hq)) h.2 r hr
  exact key QL hQ h

theorem mem_e {k : Nat} (hk : EPK k < 693) (he : EAK (EPK k) = k) : k ∈ eaPts orbL := by
  rw [← Array.mem_toList_iff, e_toList, EAL, List.mem_map]
  exact ⟨EPK k, List.mem_range.2 hk, he⟩

theorem aw_ok : (List.all (aWord () ++ aWord2 ()) fun k =>
    Nat.blt (EPK k) 693 && Nat.beq (EAK (EPK k)) k) = true := by decide +kernel

theorem aw_mem : ∀ k ∈ aWord () ++ aWord2 (), k ∈ eaPts orbL := by
  intro k hk
  have h := List.all_eq_true.1 aw_ok k hk
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact mem_e h.1 h.2

theorem lv_facts {l : Nat} (hl : l ∈ lvK LJ BJ 32 1) : l < 32 ∧ lvChk l = true := by
  obtain ⟨t, ht, rfl⟩ := exists_lvAt hl
  have h30 : (lvK LJ BJ 32 1).length = 30 := Nat.eq_of_beq_eq_true lv_len
  have ht' : t < 30 := by omega
  have hs := lvSlAll t ht'
  exact ⟨(mem_lvK.1 hl).1, hs⟩

theorem rr_eq {l : Nat} (hl : l < 32) (hc : ∀ i < 693, EPK (LJ l (EAK i)) < 693) :
    (rrImg (eaPts orbL) (ePos (eaPts orbL)) (chainLetters orbL)[l]!).toList = rrK l ∧
      ∀ x ∈ rrImg (eaPts orbL) (ePos (eaPts orbL)) (chainLetters orbL)[l]!, x < 693 := by
  have hv : ∀ u < 693, phiData[(ePos (eaPts orbL))[ap (chainLetters orbL)[l]!
      (eaPts orbL)[(phiPos ())[u]!]!]!]! = PHK (EPK (LJ l (EAK (PIK u)))) ∧
      PHK (EPK (LJ l (EAK (PIK u)))) < 693 := by
    intro u hu
    have hp := (phi_facts hu).2.1
    have hL := (letters_TR hl).2 (EAK (PIK u)) (EAK_lt hp)
    rw [phiPos_get hu, e_get hp, hL.1, p_get hL.2, phi_get (hc _ hp)]
    exact ⟨rfl, (phi_facts (hc _ hp)).1⟩
  have hr : (rrImg (eaPts orbL) (ePos (eaPts orbL)) (chainLetters orbL)[l]!).toList = rrK l := by
    unfold rrImg rrK
    rw [mapK_eq, QT_eq, Array.toList_ofFn]
    apply List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
    intro u h1 h2
    rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    exact (hv u (by rw [List.length_ofFn] at h1; exact h1)).1
  refine ⟨hr, fun x hx => ?_⟩
  rw [← Array.mem_toList_iff, hr] at hx
  unfold rrK at hx
  rw [mapK_eq, QT_eq] at hx
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
  exact (phi_facts (hc _ (phi_facts (List.mem_range.1 hu)).2.1)).1

theorem letter_ok {l : Nat} (hl : l ∈ lvK LJ BJ 32 1) :
    ((allIn 0 693 fun i => decide ((ePos (eaPts orbL))[ap (chainLetters orbL)[l]!
        (eaPts orbL)[i]!]! < 693)) &&
      sift (t46Trees ()) (t46Letters ()) t46Base (t46Q ()) 0
        (rrImg (eaPts orbL) (ePos (eaPts orbL)) (chainLetters orbL)[l]!)) = true := by
  obtain ⟨hl32, hc⟩ := lv_facts hl
  unfold lvChk at hc
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hc
  have hcl : ∀ i < 693, EPK (LJ l (EAK i)) < 693 := fun i hi =>
    Nat.blt_eq.mp (Raw.Orb.allN_iff.1 hc.1 i hi)
  have hap : ∀ i < 693, ap (chainLetters orbL)[l]! (eaPts orbL)[i]! = LJ l (EAK i) ∧
      LJ l (EAK i) < 3510 := fun i hi => by
    rw [e_get hi]
    exact (letters_TR hl32).2 _ (EAK_lt hi)
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [TW.allIn_iff]
    intro i hi
    rw [decide_eq_true_eq, (hap i hi).1, p_get (hap i hi).2]
    exact hcl i hi
  · obtain ⟨hr, hb⟩ := rr_eq hl32 hcl
    have ht : t46Trees () = trees 693 5 CNTT PTST POST PART LABT := KernelT46.chain_eq.1
    rw [ht, sift_eq KernelT46.chain_hyp 5 0 rfl _ hb, hr]
    exact hc.2

theorem gen_ok : centGenOK orbL (eaPts orbL) (ePos (eaPts orbL)) = true := by
  unfold centGenOK
  rw [TW.allIn_iff]
  intro s hs
  have hrs := rsAll s hs
  unfold rs rowSl at hrs
  have h := Raw.Orb.allN_iff.1 hrs
  unfold rowAt at h
  rw [Bool.and_eq_true, decide_eq_true_eq, TW.allIn_iff]
  have h0 := h 0 (by norm_num)
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h0
  refine ⟨h0.1, fun j hj => ?_⟩
  have hj' := h j hj
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hj'
  obtain ⟨hr, hm, hx, hu⟩ := hj'
  rw [beq_iff_eq]
  unfold cPt
  rw [e_get hr, e_get hj, cTab_eq (EAK_lt hr) (EAK_lt hj), ← hx, p_get (EAK_lt hm), EPK_EAK hm,
    phi_get hm, phi_get hr, phi_get hj, uPts_get (phi_facts hm).1, uPts_get (phi_facts hr).1,
    uPts_get (phi_facts hj).1, hu]

theorem tree_facts' : ORK 0 = GSK 0 ∧
    (∀ t < 693, ORK t < 693 ∧ (t = 0 ∨ (TPK t < t ∧ TGK t < 6 ∧
      cK (EAK (GSK (TGK t))) (EAK (ORK (TPK t))) = EAK (ORK t)))) ∧
    ∀ i < 693, OIK i < 693 ∧ ORK (OIK i) = i := by
  have h := CertificateChecks.KernelFi22Cent.tree_ok
  unfold Fi22Cent.treeK at h
  rw [Raw.Orb.bAnd_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
  refine ⟨h.1, fun t ht => ?_, fun i hi => ?_⟩
  · have h1 := Raw.Orb.allN_iff.1 h.2.1 t ht
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Raw.Orb.bIf_eq] at h1
    refine ⟨h1.1, ?_⟩
    by_cases h0 : t = 0
    · exact Or.inl h0
    · right
      have h2 := h1.2
      rw [ite_eq_right (fun hb => h0 (Nat.eq_of_beq_eq_true hb))] at h2
      simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq,
        Nat.beq_eq] at h2
      exact h2
  · have h3 := Raw.Orb.allN_iff.1 h.2.2 i hi
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h3
    exact h3

theorem GSK_lt {s : Nat} (hs : s < 6) : GSK s < 693 := by
  have hrs := rsAll s hs
  unfold rs rowSl at hrs
  have h := Raw.Orb.allN_iff.1 hrs 0 (by norm_num)
  unfold rowAt at h
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h.1

theorem tree_ok' : centTreeOK orbL (eaPts orbL) (ePos (eaPts orbL)) = true := by
  obtain ⟨h0, h1, h2⟩ := tree_facts'
  unfold centTreeOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨h0, ?_⟩, ?_⟩
  · rw [CFSG.Sporadic.Th.allIn_eq_true]
    intro t ht1 ht2
    obtain ⟨ho, hr⟩ := h1 t ht2
    rcases hr with rfl | ⟨ha, hb, hc⟩
    · omega
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    have hs := (h1 (TPK t) (by omega)).1
    have hg := GSK_lt hb
    refine ⟨⟨ha, hb⟩, ?_⟩
    unfold cPt
    rw [e_get hg, e_get hs, cTab_eq (EAK_lt hg) (EAK_lt hs), hc, p_get (EAK_lt ho), EPK_EAK ho]
  · rw [CFSG.Sporadic.Th.allIn_eq_true]
    intro i _ hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact h2 i hi

theorem cent_ok : centChecksK orbL = true := by
  unfold centChecksK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨e_size, by rw [← Array.length_toList]; exact phiData_length⟩, ?_⟩, ?_⟩, gen_ok⟩, tree_ok'⟩, ?_⟩,
    pow_ok (by decide) pow1_ok⟩, ?_⟩, pow_ok (by decide) pow2_ok⟩
  · rw [CFSG.Sporadic.Th.allIn_eq_true]
    intro i _ hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [phi_get hi, phiPos_get (phi_facts hi).1]
    exact ⟨(phi_facts hi).1, (phi_facts hi).2.2.1⟩
  · rw [lv1_eq, List.all_toArray, List.all_eq_true]
    intro l hl
    exact letter_ok hl
  · rw [List.all_eq_true]
    intro k hk
    rw [Array.contains_iff_mem]
    exact aw_mem k (List.mem_append_left _ hk)
  · rw [List.all_eq_true]
    intro k hk
    rw [Array.contains_iff_mem]
    exact aw_mem k (List.mem_append_right _ hk)

end CertificateChecks.KernelFi22Cent

end
