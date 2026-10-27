
module

public import Certificates.Kernel.Sporadic.Fi24ThreeO.Group

public section

namespace CertificateChecks.KernelFi24OrbL

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.KC.Fi24Orb CFSG.KD.Fi24Net CFSG.KS.Fi24Net CFSG.KC.Fi24Kit CFSG.KD.Fi24Kit
  CFSG.KS.Fi24Kit

attribute [local instance] CFSG.Sporadic.Fi24.rAction

theorem a_val (q : ℕ) (hq : q < 306936) :
    idx 306936 a q = oA (CFSG.KD.Fi24Orb.OL q) := by
  rw [← rep_alpha q hq, orb_alpha_orbL q hq]

theorem b_val (q : ℕ) (hq : q < 306936) :
    idx 306936 b q = oB (CFSG.KD.Fi24Orb.OL q) := by
  rw [← rep_beta q hq, orb_beta_orbL.2 q hq]

theorem smul_val {G : Type*} [Group G] [MulAction G (Fin 306936)] (g : G) (y : Fin 306936) :
    (g • y).val = idx 306936 g y.val :=
  (idx_of_lt g y.isLt).symm

theorem b_inv : b⁻¹ = b * b := by
  rw [inv_eq_iff_mul_eq_one, ← pow_three, b_cube]

theorem sN (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by cases y <;> rfl

theorem nIf_true {t e : ℕ} : Bool.rec (motive := fun _ => ℕ) e t true = t := rfl

theorem nIf_false {t e : ℕ} : Bool.rec (motive := fun _ => ℕ) e t false = e := rfl

theorem beq_ne {k : ℕ} (hk : k ≠ 0) : Nat.beq k 0 = false := by
  cases h : Nat.beq k 0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true h) hk

theorem dnF_zero (f q : ℕ) : dnF CFSG.KD.Fi24Orb.OL (f + 1) 0 q = q := rfl

theorem upF_zero (f q : ℕ) : upF CFSG.KD.Fi24Orb.OL (f + 1) 0 q = q := rfl

theorem dnF_succ (f : ℕ) {k : ℕ} (hk : k ≠ 0) (q : ℕ) :
    dnF CFSG.KD.Fi24Orb.OL (f + 1) k q = gT CFSG.KD.Fi24Orb.OL (oLab (CFSG.KD.Fi24Orb.OL k))
      (dnF CFSG.KD.Fi24Orb.OL f (oPar (CFSG.KD.Fi24Orb.OL k)) q) := by
  change Bool.rec (motive := fun _ => ℕ) (CFSG.KC.Loop.strictN (CFSG.KD.Fi24Orb.OL k) fun e =>
    CFSG.KC.Loop.strictN (dnF CFSG.KD.Fi24Orb.OL f (oPar e) q)
      (gT CFSG.KD.Fi24Orb.OL (oLab e))) q (Nat.beq k 0) = _
  simp only [beq_ne hk, sN]

theorem upF_succ (f : ℕ) {k : ℕ} (hk : k ≠ 0) (q : ℕ) :
    upF CFSG.KD.Fi24Orb.OL (f + 1) k q = upF CFSG.KD.Fi24Orb.OL f (oPar (CFSG.KD.Fi24Orb.OL k))
      (gI CFSG.KD.Fi24Orb.OL (oLab (CFSG.KD.Fi24Orb.OL k)) q) := by
  change Bool.rec (motive := fun _ => ℕ) (CFSG.KC.Loop.strictN (CFSG.KD.Fi24Orb.OL k) fun e =>
    CFSG.KC.Loop.strictN (gI CFSG.KD.Fi24Orb.OL (oLab e) q)
      (upF CFSG.KD.Fi24Orb.OL f (oPar e))) q (Nat.beq k 0) = _
  simp only [beq_ne hk, sN]

theorem tree_elt : ∀ k (hk : k < 306936), ∃ u : J, u • root = (⟨k, hk⟩ : Fin 306936) ∧
    (∀ f > k, ∀ q < 306936, dnF CFSG.KD.Fi24Orb.OL f k q = idx 306936 u q) ∧
    (∀ f > k, ∀ q < 306936, upF CFSG.KD.Fi24Orb.OL f k q = idx 306936 u⁻¹ q) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · refine ⟨1, one_smul _ _, fun f hf q _ => ?_, fun f hf q _ => ?_⟩
      · obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rw [dnF_zero, idx_one]
      · obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rw [upF_zero, inv_one, idx_one]
    · obtain ⟨hp, hl⟩ := CertificateChecks.KernelFi24Orb.tree hk (by omega)
      set p := oPar (CFSG.KD.Fi24Orb.OL k) with hpdef
      obtain ⟨u, hu, hd, hup⟩ := ih p hp (by omega)
      have key : ∃ g : J, (∀ q < 306936, gT CFSG.KD.Fi24Orb.OL (oLab (CFSG.KD.Fi24Orb.OL k)) q =
          idx 306936 g q) ∧ (∀ q < 306936, gI CFSG.KD.Fi24Orb.OL (oLab (CFSG.KD.Fi24Orb.OL k)) q =
          idx 306936 g⁻¹ q) ∧ idx 306936 g p = k := by
        rcases hl with ⟨h1, he⟩ | ⟨h2, he⟩
        · refine ⟨a, fun q hq => ?_, fun q hq => ?_, ?_⟩
          · unfold gT
            rw [h1, a_val q hq]
            rfl
          · unfold gI
            rw [h1, a_inv, a_val q hq]
            rfl
          · rw [a_val p (by omega)]
            exact he
        · refine ⟨b, fun q hq => ?_, fun q hq => ?_, ?_⟩
          · unfold gT
            rw [h2, b_val q hq]
            rfl
          · unfold gI
            rw [h2, b_inv, idx_mul, b_val q hq, b_val _ (by rw [← b_val q hq]; exact idx_lt _ hq)]
            simp only [show Nat.beq 2 1 = false from rfl, sN]
          · rw [b_val p (by omega)]
            exact he
      obtain ⟨g, hgT, hgI, hgp⟩ := key
      refine ⟨g * u, ?_, fun f hf q hq => ?_, fun f hf q hq => ?_⟩
      · apply Fin.ext
        rw [mul_smul, hu, ← idx_of_lt g (by omega : p < 306936)]
        exact hgp
      · obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rw [dnF_succ f (by omega), hd f (by omega) q hq, hgT _ (idx_lt _ hq), idx_mul]
      · obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rw [upF_succ f (by omega), hgI q hq, hup f (by omega) _ (idx_lt _ hq), ← idx_mul,
          mul_inv_rev]

@[expose] def conv (z : ℤ) : ℕ := if 0 < z then 2 * (z.natAbs - 1) else 2 * (z.natAbs - 1) + 1

theorem genLetterG_eq {z : ℤ} (hz : z ≠ 0) : genLetterG z = pairG gs (conv z) := by
  unfold genLetterG conv pairG
  by_cases h : 0 < z
  · rw [if_pos h, if_pos h, if_pos (by omega)]
    congr 1
    omega
  · rw [if_neg h, if_neg h, if_neg (by omega)]
    congr 2
    omega

theorem extWord_val : ∀ (w : List ℤ), (∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 13) → ∀ y < 306936,
    idx 306936 (extWord w) y = wN NW (w.map conv) y ∧ wN NW (w.map conv) y < 306936
  | [], _, y, hy => by
    refine ⟨?_, hy⟩
    change idx 306936 ((List.map genLetterG []).prod) y = y
    rw [List.map_nil, List.prod_nil, idx_one]
  | z :: w, hw, y, hy => by
    obtain ⟨ih1, ih2⟩ := extWord_val w (fun z' h => hw z' (List.mem_cons_of_mem z h)) y hy
    obtain ⟨hz0, hz13⟩ := hw z List.mem_cons_self
    have hc : conv z < 26 := by unfold conv; split_ifs <;> omega
    have e : extWord (z :: w) = genLetterG z * extWord w := by
      unfold extWord wordG
      rw [List.map_cons, List.prod_cons]
    change idx 306936 (extWord (z :: w)) y = LN NW (conv z) (wN NW (w.map conv) y) ∧
      LN NW (conv z) (wN NW (w.map conv) y) < 306936
    rw [e, idx_mul, ih1, genLetterG_eq hz0, pairG_LN _ hc _ ih2]
    exact ⟨rfl, LN_lt_N hc ih2⟩

theorem wA_eq : normWords[0]!.map conv = wA := by decide

theorem wB_eq : normWords[1]!.map conv = wB := by decide

theorem normWords_ok : ∀ i < 2, ∀ z ∈ normWords[i]!, z ≠ 0 ∧ z.natAbs ≤ 13 := by decide

theorem nA_val (y : ℕ) (hy : y < 306936) : idx 306936 nA y = wN NW wA y := by
  rw [← wA_eq]
  exact (extWord_val _ (normWords_ok 0 (by norm_num)) y hy).1

theorem nB_val (y : ℕ) (hy : y < 306936) : idx 306936 nB y = wN NW wB y := by
  rw [← wB_eq]
  exact (extWord_val _ (normWords_ok 1 (by norm_num)) y hy).1

theorem tPerm_val : ∀ p : Fin 306936, (tPerm p).val = pF NT p.val := by
  have key : ∀ k, ∀ hk : k < 306936, (tPerm ⟨k, hk⟩).val = pF NT k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [show (⟨0, hk⟩ : Fin 306936) = root from rfl, tPerm_root, tP_facts.2.1]
      · obtain ⟨hp, hl⟩ := CertificateChecks.KernelFi24Orb.tree hk (by omega)
        set p := oPar (CFSG.KD.Fi24Orb.OL k) with hpdef
        have hpN : p < 306936 := by omega
        have ihp := ih p hp hpN
        rcases hl with ⟨-, he⟩ | ⟨-, he⟩
        · have hk' : (⟨k, hk⟩ : Fin 306936) = a • (⟨p, hpN⟩ : Fin 306936) := by
            apply Fin.ext
            rw [← idx_of_lt a hpN, a_val p hpN]
            exact he.symm
          rw [hk', tPerm_smul, tAut_a, smul_val, ihp, nA_val _ (tP_facts.2.2.1 p hpN),
            ← (tP_facts.2.2.2 p hpN).1]
          change pF NT (CertificateChecks.KernelFi24Orb.α p) = _
          rw [he]
        · have hk' : (⟨k, hk⟩ : Fin 306936) = b • (⟨p, hpN⟩ : Fin 306936) := by
            apply Fin.ext
            rw [← idx_of_lt b hpN, b_val p hpN]
            exact he.symm
          rw [hk', tPerm_smul, tAut_b, smul_val, ihp, nB_val _ (tP_facts.2.2.1 p hpN),
            ← (tP_facts.2.2.2 p hpN).2]
          change pF NT (CertificateChecks.KernelFi24Orb.β p) = _
          rw [he]
  intro p
  exact key p.val p.isLt

theorem bridge : CFSG.KD.Fi24ThreeO.Group.Bridge where
  letter := fun l hl x => by
    rw [smul_val]
    exact pairG_LN l hl x.val x.isLt
  cls := fun k p => by
    change (cls k • p).val = clsK CFSG.KD.Fi24Orb.OL NT k.val p.val
    obtain ⟨u, hu, hd, hup⟩ := tree_elt k.val k.isLt
    have hk : jR u • root = k := by
      rw [jR_smul, hu]
    have e : clsK CFSG.KD.Fi24Orb.OL NT k.val p.val = dnF CFSG.KD.Fi24Orb.OL (k.val + 1) k.val
        (pF NT (upF CFSG.KD.Fi24Orb.OL (k.val + 1) k.val p.val)) := by
      unfold clsK dnT upI
      rw [sN, sN, CFSG.KS.Fi24NetPt.ptF_eq]
    have hlt : pF NT (idx 306936 u⁻¹ p.val) < 306936 := tP_facts.2.2.1 _ (idx_lt _ p.isLt)
    rw [e, hup _ (by omega) _ p.isLt, hd _ (by omega) _ hlt, cls_eq_conj_of_smul_root hk,
      mul_smul, mul_smul, ← map_inv, jR_smul, tR_smul, jR_smul, smul_val, tPerm_val, smul_val]

end CertificateChecks.KernelFi24OrbL
