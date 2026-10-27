
module

public import Certificates.Kernel.Fi22Inv.Checks
public import Certificates.Kernel.Fi22Syl.Final
public import Certificates.Kernel.Fi22Cent.Final
public import CFSG.Sporadic.Fi22.InvFixBase
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases
public import CFSG.Fischer.T46Unitary
public import CFSG.Sporadic.Fi22.InvCertBase
public import CFSG.Sporadic.Fi22.Nfp

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelFi22I.repAll CertificateChecks.KernelFi22I.repSl 27
#kon_join CertificateChecks.KernelFi22I.fixAll CertificateChecks.KernelFi22I.fixSl 128

namespace CertificateChecks.KernelFi22I

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.TW
  CFSG.KS.Fi22S CFSG.KS.Fi22Cent CFSG.KS.Fi22I CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CertificateChecks.KernelFi22S CertificateChecks.KernelFi22Cent

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem foldr_count (F : Nat → Nat) : ∀ l : List Nat,
    l.foldr (fun i s => Bool.rec (motive := fun _ => Nat) s (Nat.succ s) (Nat.beq (F i) i)) 0 =
      l.countP fun i => F i == i
  | [] => rfl
  | a :: l => by
    rw [List.foldr_cons, foldr_count F l, List.countP_cons]
    by_cases h : F a = a
    · have e : Nat.beq (F a) a = true := by rw [Nat.beq_eq]; exact h
      rw [e]
      simp [h]
    · have e : Nat.beq (F a) a = false := by
        rw [Bool.eq_false_iff]
        intro h'
        exact h (Nat.eq_of_beq_eq_true h')
      rw [e]
      simp [h]

theorem cntK_eq (F : Nat → Nat) : cntK F = (List.range 3510).countP fun i => F i == i := by
  unfold cntK
  rw [Raw.Orb.foldN_eq]
  exact foldr_count F _

theorem countP_congr' {F G : Nat → Nat} (h : ∀ x < 3510, F x = G x) :
    ((List.range 3510).countP fun i => F i == i) = (List.range 3510).countP fun i => G i == i :=
  List.countP_congr fun i hi => by rw [h i (List.mem_range.1 hi)]

theorem countP_idx (g : J) {F : Nat → Nat} (h : ∀ x < 3510, F x = idx 3510 g x) :
    ((List.range 3510).countP fun i => F i == i) =
      (Finset.univ.filter fun i : Fin 3510 => g • i = i).card := by
  rw [card_fixed_eq_countP]
  exact countP_congr' h

theorem inS_spec {c : Nat} (h : inS c = true) : c = 54 ∨ c = 182 ∨ c = 694 := by
  unfold inS at h
  simp only [Raw.Orb.bIf_eq] at h
  split_ifs at h with h1 h2
  · exact Or.inl (Nat.eq_of_beq_eq_true h1)
  · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
  · exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true h))

theorem rep_of {r : Nat} (hr : r < 54) : repChk r = true := by
  have hs : r / 2 < 27 := by omega
  have h := repAll (r / 2) hs
  unfold repSl at h
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  rcases Nat.even_or_odd' r with ⟨c, rfl | rfl⟩
  · have e : 2 * c / 2 = c := by omega
    rw [e] at h
    exact h.1
  · have e : (2 * c + 1) / 2 = c := by omega
    rw [e] at h
    exact h.2

theorem fixLeafK_of {k j : Nat} (hk : k < 1024) (hj : j < 128) : fixLeafK k j = true := by
  have hs : k / 8 < 128 := by omega
  have h := fixAll (k / 8) hs
  unfold fixSl at h
  have h' := Raw.Orb.allN_iff.1 h (k % 8) (Nat.mod_lt _ (by norm_num))
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add (Nat.mul (k / 8) 8) (k % 8) = k := Nat.div_add_mod' k 8
  rw [e] at h'
  exact Raw.Orb.allN_iff.1 h' j hj

theorem conjQ_spec (D G R : Nat → Nat) : ∀ l : List Nat,
    List.rec (motive := fun _ => Bool) true
      (fun q _ ih => bAnd(Nat.beq (strictN (G q) D) (strictN (D q) R), ih)) l = true →
      ∀ q ∈ l, D (G q) = R (D q)
  | [], _ => by simp
  | a :: l, h => by
    change bAnd(Nat.beq (strictN (G a) D) (strictN (D a) R), List.rec (motive := fun _ => Bool) true
      (fun q _ ih => bAnd(Nat.beq (strictN (G q) D) (strictN (D q) R), ih)) l) = true at h
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Raw.Orb.strictN_eq, Raw.Orb.strictN_eq] at h
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1
    · exact conjQ_spec D G R l h.2 q hq

theorem count_conj {D G R : Nat → Nat} (hD : InJ D) (hG : InJ G) (hR : InJ R)
    (h : conjQ D G R = true) :
    ((List.range 3510).countP fun i => G i == i) = (List.range 3510).countP fun i => R i == i := by
  obtain ⟨d, hd⟩ := hD
  obtain ⟨g, hg⟩ := hG
  obtain ⟨r, hr⟩ := hR
  have hq := conjQ_spec D G R QL h
  have e : (r * d)⁻¹ * (d * g) = 1 := sep _ fun t ht => by
    have hm : chainQ[t]! ∈ QL := by
      rw [← chain_hyp.chk.1, getElem!_pos chainQ t ht]
      exact Array.getElem_mem_toList ht
    have hl := QL_lt _ hm
    have h1 := hq _ hm
    rw [hg _ hl, hd _ (idx_lt g hl), hd _ hl, hr _ (idx_lt d hl), ← idx_mul, ← idx_mul] at h1
    rw [idx_mul, h1, ← idx_mul, inv_mul_cancel, idx_one]
  have e2 : d * g * d⁻¹ = r := by
    rw [inv_mul_eq_one] at e
    rw [← e, mul_inv_cancel_right]
  rw [countP_idx g hg, countP_idx r hr, ← e2, card_fixed_conj]

theorem ab_eq {k j : Nat} (hk : k < 1024) (hj : j < 128) :
    ∀ x < 3510, ap (tabK 0)[k]! (ap (tabK 1)[j]! x) = gK k j x := by
  obtain ⟨c0, c1⟩ := cnts
  intro x hx
  have t1 := (tab_TR (i := 1) (by norm_num) (by rw [c1]; exact hj)).2 x hx
  rw [t1.1, ((tab_TR (i := 0) (by norm_num) (by rw [c0]; exact hk)).2 _ t1.2).1]
  unfold gK
  rw [Raw.Orb.strictN_eq]

theorem fixLeaf_ok {k j : Nat} (hk : k < 1024) (hj : j < 128) :
    fixLeaf (tabK 0)[k]! (tabK 1)[j]! = true := by
  have hAB := ab_eq hk hj
  have hG := inJ_gK hk hj
  have hl := fixLeafK_of hk hj
  unfold fixLeafK at hl
  rw [Raw.Orb.bIf_eq, Raw.Orb.bIf_eq] at hl
  unfold fixLeaf
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
  split_ifs at hl with h1 h2
  · obtain ⟨q, hq, hne⟩ := anyMv_spec h1
    have hq' := QL_lt q hq
    refine Or.inl (Or.inl (not_allIn hq' ?_))
    rw [hAB q hq', hAB _ (hG.lt hq')]
    unfold KernelFi22S.sq at hne
    rw [Raw.Orb.strictN_eq] at hne
    simpa using hne
  · refine Or.inl (Or.inr ?_)
    rw [TW.allIn_iff]
    intro i hi
    rw [hAB i hi, hG.eq_id h2 i hi, beq_self_eq_true]
  · rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.strictB_eq,
      Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.bAnd_eq,
      Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, Nat.blt_eq, Nat.blt_eq] at hl
    obtain ⟨-, hr, hk', hj', hc⟩ := hl
    have hrep := rep_of hr
    unfold repChk at hrep
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.bAnd_eq,
      Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq] at hrep
    obtain ⟨rk, rj, hS, hcnt⟩ := hrep
    refine Or.inr ?_
    rw [cntK_eq] at hcnt
    rw [countP_congr' hAB, count_conj (inJ_gK hk' hj') hG (inJ_gK rk rj) hc, hcnt]
    rcases inS_spec hS with e | e | e
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr e)
    · exact Or.inr e

theorem bIf_true (c e : Bool) : Bool.rec (motive := fun _ => Bool) e true c = (c || e) := by
  cases c <;> rfl

theorem fix2_iff (a b : Nat) : ∀ ws : List Nat,
    fix2 ws a b = true ↔ ∀ k ∈ ws, cK k a = a ∧ cK k b = b
  | [] => by simp [fix2]
  | k :: ws => by
    change bAnd(Nat.beq (cK k a) a, bAnd(Nat.beq (cK k b) b, fix2 ws a b)) = true ↔ _
    rw [Raw.Orb.bAnd_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq,
      Nat.beq_eq, fix2_iff a b ws, List.forall_mem_cons, and_assoc]

theorem mvW_iff (p : Nat) : ∀ ws : List Nat, mvW ws p = true ↔ ∃ k ∈ ws, cK k p ≠ p
  | [] => by simp [mvW]
  | k :: ws => by
    change Bool.rec (motive := fun _ => Bool) true (mvW ws p) (Nat.beq (cK k p) p) = true ↔ _
    rw [Raw.Orb.bIf_eq]
    by_cases h : cK k p = p
    · rw [ite_eq_left (by rw [Nat.beq_eq]; exact h), mvW_iff p ws]
      simp [h]
    · rw [ite_eq_right (by rw [Nat.beq_eq]; exact h)]
      simp only [true_iff]
      exact ⟨k, List.mem_cons_self, h⟩

theorem map_cTab_all {ws : List Nat} (hw : ∀ k ∈ ws, k < 3510) {a b : Nat} (ha : a < 3510)
    (hb : b < 3510) (h : fix2 ws a b = true) :
    (ws.toArray.map (cTab orbL (genTables orbL (-2)))).all (fun T => ap T a == a && ap T b == b) =
      true := by
  rw [Array.all_eq_true']
  intro T hT
  obtain ⟨k, hk, rfl⟩ := Array.mem_map.1 hT
  rw [List.mem_toArray] at hk
  obtain ⟨e1, e2⟩ := (fix2_iff a b ws).1 h k hk
  rw [cTab_eq (hw k hk) ha, cTab_eq (hw k hk) hb, e1, e2, beq_self_eq_true, beq_self_eq_true]
  rfl

theorem map_cTab_any {ws : List Nat} (hw : ∀ k ∈ ws, k < 3510) {p : Nat} (hp : p < 3510)
    (h : mvW ws p = true) :
    (ws.toArray.map (cTab orbL (genTables orbL (-2)))).any (fun T => ap T p != p) = true := by
  obtain ⟨k, hk, hne⟩ := (mvW_iff p ws).1 h
  rw [Array.any_eq_true']
  refine ⟨_, Array.mem_map_of_mem (List.mem_toArray.2 hk), ?_⟩
  rw [cTab_eq (hw k hk) hp, bne_iff_ne]
  exact hne

theorem alpha_eq {x : Nat} (hx : x < 3510) : ap orbL.alpha x = Fi22Cent.gA x :=
  (KernelFi22C.alpha_get hx).1

theorem stab_native : stabChecks orbL = true := by
  have s := stab_ok
  unfold stabK at s
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at s
  obtain ⟨f1, f2, a8, a1, h1, h2⟩ := s
  have hw1 : ∀ k ∈ wit1L, k < 3510 := by decide
  have hw2 : ∀ k ∈ wit2L, k < 3510 := by decide
  have e1 : wit1 = wit1L.toArray := rfl
  have e2 : wit2 = wit2L.toArray := rfl
  have es : subRoot () = 8 := rfl
  unfold stabChecks
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨by rw [e1, List.all_toArray]; decide, by rw [e2, List.all_toArray]; decide⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [e1]
    exact map_cTab_all hw1 (by norm_num) (by norm_num) f1
  · rw [e2, es]
    exact map_cTab_all hw2 (by norm_num) (by norm_num) f2
  · rw [es, alpha_eq (by norm_num), beq_iff_eq]
    exact Nat.eq_of_beq_eq_true a8
  · rw [es, alpha_eq (by norm_num), bne_iff_ne]
    intro e
    rw [e, Raw.Orb.bIf_eq, ite_eq_left (Nat.beq_refl 8)] at a1
    exact absurd a1 (by decide)
  · rw [TW.allIn_iff]
    intro p hp
    have h := Raw.Orb.allN_iff.1 h1 p hp
    simp only [bIf_true] at h
    rw [alpha_eq (by norm_num)]
    simp only [Bool.or_eq_true, beq_iff_eq] at h ⊢
    rcases h with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Nat.eq_of_beq_eq_true h)))
    · exact Or.inl (Or.inl (Or.inr (Nat.eq_of_beq_eq_true h)))
    · exact Or.inl (Or.inr (Nat.eq_of_beq_eq_true h))
    · rw [e1]
      exact Or.inr (map_cTab_any hw1 hp h)
  · rw [TW.allIn_iff]
    intro p hp
    have h := Raw.Orb.allN_iff.1 h2 p hp
    simp only [bIf_true] at h
    rw [es]
    simp only [Bool.or_eq_true, beq_iff_eq] at h ⊢
    rcases h with h | h | h
    · exact Or.inl (Or.inl (Nat.eq_of_beq_eq_true h))
    · exact Or.inl (Or.inr (Nat.eq_of_beq_eq_true h))
    · rw [e2]
      exact Or.inr (map_cTab_any hw2 hp h)

theorem fixExact_of {w : List Nat} {c : Nat} (hw : ∀ k ∈ w, k < 3510) (h : attK w c = true) :
    fixExact (wordTab orbL (genTables orbL (-2)) w) c = true := by
  have hP := fun x (hx : x < 3510) => wordTab_eq w hw hx
  unfold attK at h
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hi, hm, hc⟩ := h
  unfold fixExact
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold Native.invoOK
    rw [TW.allIn_iff]
    intro i hi'
    rw [(hP i hi').1, (hP _ (hP i hi').2).1, beq_iff_eq]
    exact Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 hi i hi')
  · obtain ⟨q, hq, hne⟩ := anyMv_spec hm
    have hq' := QL_lt q hq
    refine not_allIn hq' ?_
    rw [(hP q hq').1]
    simpa using hne
  · rw [cntK_eq] at hc
    rw [countP_congr' fun x hx => (hP x hx).1, hc]

theorem attain_native : attainChecks orbL = true := by
  have h := att_ok
  unfold attAllK at h
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2⟩ := h
  unfold attainChecks
  rw [Array.all_eq_true]
  intro i hi
  change i < 3 at hi
  interval_cases i
  · change (([0] : List Nat).all (· < 3510) && fixExact (wordTab orbL (genTables orbL (-2)) [0])
      694) = true
    rw [fixExact_of (by decide) h0]
    rfl
  · change (([0, 8] : List Nat).all (· < 3510) &&
      fixExact (wordTab orbL (genTables orbL (-2)) [0, 8]) 182) = true
    rw [fixExact_of (by decide) h1]
    rfl
  · change (([0, 8, 31] : List Nat).all (· < 3510) &&
      fixExact (wordTab orbL (genTables orbL (-2)) [0, 8, 31]) 54) = true
    rw [fixExact_of (by decide) h2]
    rfl

theorem inv_ok : invChecks orbL 3 = true := by
  obtain ⟨c0, c1⟩ := cnts
  unfold invChecks
  simp only [Bool.and_eq_true]
  refine ⟨⟨stab_native, attain_native⟩, ?_⟩
  apply parAll_of
  intro k hk
  change k < (tabK 0).size at hk
  rw [tabK_size (by norm_num), c0] at hk
  rw [Array.all_eq_true]
  intro j hj
  change j < (tabK 1).size at hj
  have hj' := hj
  rw [tabK_size (by norm_num), c1] at hj'
  rw [← getElem!_pos (tabK 1) j hj]
  exact fixLeaf_ok hk hj'

end CertificateChecks.KernelFi22I

end
