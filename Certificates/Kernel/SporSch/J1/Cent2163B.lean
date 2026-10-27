module

public import Certificates.Kernel.SporSch.J1.Cent2163A
public import Certificates.Kernel.SporSch.J1.DClo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CIdx
open CFSG.KS.SporSch.J1C CFSG.KS.KeyBfs CFSG.KS.Tbl CFSG.KS.ClassLab
open CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem prep_wordP {L : Int → Nat} {gL : Int → Equiv.Perm (Fin 3080)} :
    ∀ wd : List Int, (∀ l ∈ wd, PRep 3080 12 (L l) (gL l)) →
      PRep 3080 12 (wordP 3080 12 (mask 12) (pidn 3080 12) L wd)
        (CFSG.Sporadic.Th.wordG gL wd)
  | [], _ => by
    simpa [wordP, CFSG.Sporadic.Th.wordG] using prep_pidn (n := 3080) (w := 12) (by norm_num)
      (by norm_num)
  | l :: wd, h => by
    have ih := prep_wordP wd fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have := prep_pcomp n32 (h l List.mem_cons_self) ih
    simpa [wordP, CFSG.Sporadic.Th.wordG] using this

theorem prep_eq {P : Nat} {g h : Equiv.Perm (Fin 3080)} (hg : PRep 3080 12 P g)
    (hh : PRep 3080 12 P h) : g = h :=
  Equiv.ext fun x => Fin.ext (by rw [← hg x, ← hh x])

theorem prep_inv {P Q : Nat} {g : Equiv.Perm (Fin 3080)} (hg : PRep 3080 12 P g)
    (h : permOK 3080 12 (mask 12) (3080 * 12) P Q = true) : PRep 3080 12 Q g⁻¹ := by
  obtain ⟨-, -, h3⟩ := permOK_facts h
  intro x
  have hy := (g⁻¹ x).isLt
  have e := (h3 _ hy).2
  rw [hg ⟨_, hy⟩] at e
  simpa using e

theorem wordG_mem {gL : Int → Equiv.Perm (Fin 3080)} (h : ∀ l, gL l ∈ GJ) :
    ∀ wd : List Int, CFSG.Sporadic.Th.wordG gL wd ∈ GJ := fun wd =>
  Subgroup.list_prod_mem _ (by simpa using fun l _ => h l)

noncomputable abbrev aG (l : Int) : Equiv.Perm (Fin 3080) :=
  if l = 1 then ea else if l = -1 then ea⁻¹ else if l = 2 then eb else eb⁻¹

theorem rep_letter (l : Int) : CFSG.Sporadic.Th.Rep 3080 (j1LetterTbl l) (aG l) := by
  unfold j1LetterTbl aG
  split_ifs
  · exact rep_A
  · exact rep_AI
  · exact rep_B
  · exact rep_BI

theorem aG_mem (l : Int) : aG l ∈ GJ := by
  unfold aG
  split_ifs
  · exact ea_mem
  · exact Subgroup.inv_mem _ ea_mem
  · exact eb_mem
  · exact Subgroup.inv_mem _ eb_mem

theorem prep_ltrA {l : Int} (hl : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) :
    PRep 3080 12 (ltrK J1L.S J1L.SI l) (aG l) := by
  rcases hl with rfl | rfl | rfl | rfl
  · rw [show aG 1 = ea from ite_eq_left rfl]
    exact (prepS 0 (by norm_num)).1
  · rw [show aG (-1) = ea⁻¹ by unfold aG; rw [ite_eq_right (by decide), ite_eq_left rfl]]
    exact (prepS 0 (by norm_num)).2
  · rw [show aG 2 = eb by unfold aG; rw [ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left rfl]]
    exact (prepS 1 (by norm_num)).1
  · rw [show aG (-2) = eb⁻¹ by unfold aG; rw [ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide)]]
    exact (prepS 1 (by norm_num)).2

noncomputable abbrev cG (i : Nat) : Equiv.Perm (Fin 3080) :=
  CFSG.Sporadic.Th.wordG aG (j1CWords.getD i [])

theorem rep_cT (i : Nat) : CFSG.Sporadic.Th.Rep 3080 (j1CTbl i) (cG i) :=
  CFSG.Sporadic.Th.Rep.wordT n32 _ fun l _ => rep_letter l

theorem cG_mem (i : Nat) : cG i ∈ GJ := wordG_mem aG_mem _

theorem lettersCB : (List.range 4).all (fun i => (j1CWords.getD i []).all fun l =>
    l == 1 || l == -1 || l == 2 || l == -2) = true := by
  quickRfl

theorem lettersC : ∀ i < 4, ∀ l ∈ j1CWords.getD i [], l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by
  intro i hi l hl
  have := List.all_eq_true.1 (List.all_eq_true.1 lettersCB i (List.mem_range.2 hi)) l hl
  simpa [or_assoc] using this

theorem prep_C {i : Nat} (hi : i < 4) :
    PRep 3080 12 (J1W.C i) (cG i) ∧ PRep 3080 12 (J1W.CI i) (cG i)⁻¹ := by
  have hp : PRep 3080 12 (wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK J1L.S J1L.SI)
      (j1CWords.getD i [])) (cG i) := prep_wordP _ fun l hl => prep_ltrA (lettersC i hi l hl)
  have hC : J1W.C i = wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK J1L.S J1L.SI)
      (j1CWords.getD i []) := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact Nat.eq_of_beq_eq_true J1W.C0.eq
    · exact Nat.eq_of_beq_eq_true J1W.C1.eq
    · exact Nat.eq_of_beq_eq_true J1W.C2.eq
    · exact Nat.eq_of_beq_eq_true J1W.C3.eq
  rw [← hC] at hp
  exact ⟨hp, prep_inv hp (allN_iff.1 J1W.permC i hi)⟩

noncomputable abbrev cLG (l : Int) : Equiv.Perm (Fin 3080) :=
  if 0 < l then cG (l.toNat - 1) else (cG ((-l).toNat - 1))⁻¹

theorem rep_letterC (l : Int) : CFSG.Sporadic.Th.Rep 3080 (j1CLetterTbl l) (cLG l) := by
  unfold j1CLetterTbl cLG
  split_ifs
  · exact rep_cT _
  · exact invT_rep n32 (rep_cT _)

theorem cLG_mem (l : Int) : cLG l ∈ GJ := by
  unfold cLG
  split_ifs
  · exact cG_mem _
  · exact Subgroup.inv_mem _ (cG_mem _)

theorem prep_ltrC {l : Int} (hl : (0 < l ∧ l ≤ 4) ∨ (l < 0 ∧ -4 ≤ l)) :
    PRep 3080 12 (ltrK J1W.C J1W.CI l) (cLG l) := by
  rcases l with k | k
  · simp only [Int.ofNat_eq_natCast] at hl
    have hk : 0 < k ∧ k ≤ 4 := by omega
    have e : cLG (Int.ofNat k) = cG (k - 1) := by
      unfold cLG
      rw [ite_eq_left (by simp only [Int.ofNat_eq_natCast]; omega)]
      rfl
    rw [e]
    exact (prep_C (i := k - 1) (by omega)).1
  · simp only [Int.negSucc_eq] at hl
    have hk : k < 4 := by omega
    have e : cLG (Int.negSucc k) = (cG k)⁻¹ := by
      unfold cLG
      rw [ite_eq_right (by omega)]
      rfl
    rw [e]
    exact (prep_C hk).2

noncomputable abbrev dG (j : Nat) : Equiv.Perm (Fin 3080) :=
  CFSG.Sporadic.Th.wordG cLG (j1DWords.getD j [])

theorem rep_dT (j : Nat) : CFSG.Sporadic.Th.Rep 3080 (j1DTbl j) (dG j) :=
  CFSG.Sporadic.Th.Rep.wordT n32 _ fun l _ => rep_letterC l

theorem dG_mem (j : Nat) : dG j ∈ GJ := wordG_mem cLG_mem _

theorem lettersDB : (List.range 3).all (fun j => (j1DWords.getD j []).all fun l =>
    (decide (0 < l) && decide (l ≤ 4)) || (decide (l < 0) && decide (-4 ≤ l))) = true := by
  quickRfl

theorem lettersD : ∀ j < 3, ∀ l ∈ j1DWords.getD j [], (0 < l ∧ l ≤ 4) ∨ (l < 0 ∧ -4 ≤ l) := by
  intro j hj l hl
  have := List.all_eq_true.1 (List.all_eq_true.1 lettersDB j (List.mem_range.2 hj)) l hl
  simpa using this

theorem prep_D {j : Nat} (hj : j < 3) : PRep 3080 12 (J1W.D j) (dG j) := by
  have hp : PRep 3080 12 (wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK J1W.C J1W.CI)
      (j1DWords.getD j [])) (dG j) := prep_wordP _ fun l hl => prep_ltrC (lettersD j hj l hl)
  have hD : J1W.D j = wordP 3080 12 (mask 12) (pidn 3080 12) (ltrK J1W.C J1W.CI)
      (j1DWords.getD j []) := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exact Nat.eq_of_beq_eq_true J1W.D0.eq
    · exact Nat.eq_of_beq_eq_true J1W.D1.eq
    · exact Nat.eq_of_beq_eq_true J1W.D2.eq
  rw [← hD] at hp
  exact hp

theorem c_checks : (List.range 4).all (fun i => invOK 3080 (j1CTbl i) (j1CInvTbl i)) = true := by
  rw [List.all_eq_true]
  intro i _
  exact invOK_invT n32 (rep_cT i)

theorem commT_iff {x y : Table} {g h : Equiv.Perm (Fin 3080)}
    (hx : CFSG.Sporadic.Th.Rep 3080 x g) (hy : CFSG.Sporadic.Th.Rep 3080 y h) :
    commT 3080 x y = true ↔ g * h = h * g := by
  unfold commT
  exact tblEq_iff_eq (CFSG.Sporadic.Th.Rep.compT hx hy) (CFSG.Sporadic.Th.Rep.compT hy hx)

theorem d_checks : (List.range 3).all (fun j => invOK 3080 (j1DTbl j) (invT 3080 (j1DTbl j)) &&
    commT 3080 (j1DTbl j) j1ATbl) = true ∧ commT 3080 (j1DTbl 0) (j1DTbl 2) = false := by
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro j hj
    have hj3 := List.mem_range.1 hj
    rw [Bool.and_eq_true, invOK_invT n32 (rep_dT j), commT_iff (rep_dT j) rep_A]
    refine ⟨rfl, ?_⟩
    have e := Nat.eq_of_beq_eq_true (allN_iff.1 J1W.commD j hj3)
    exact prep_eq (e ▸ prep_pcomp n32 (prep_D hj3) (prepS 0 (by norm_num)).1)
      (prep_pcomp n32 (prepS 0 (by norm_num)).1 (prep_D hj3))
  · rw [Bool.eq_false_iff]
    intro h
    rw [commT_iff (rep_dT 0) (rep_dT 2)] at h
    have hn := J1W.ncommD
    rw [Bool.not_eq_true', Bool.eq_false_iff] at hn
    apply hn
    rw [allN_iff]
    intro x hx
    rw [Nat.beq_eq, prep_pcomp n32 (prep_D (by norm_num)) (prep_D (by norm_num)) ⟨x, hx⟩,
      prep_pcomp n32 (prep_D (by norm_num)) (prep_D (by norm_num)) ⟨x, hx⟩, h]

theorem triple0 {α : Type} [Inhabited α] (a b c : α) : (#[a, b, c] : Array α)[0]! = a := by
  rw [getElem!_pos _ 0 (by simp)]
  rfl

theorem triple1 {α : Type} [Inhabited α] (a b c : α) : (#[a, b, c] : Array α)[1]! = b := by
  rw [getElem!_pos _ 1 (by simp)]
  rfl

theorem triple2 {α : Type} [Inhabited α] (a b c : α) : (#[a, b, c] : Array α)[2]! = c := by
  rw [getElem!_pos _ 2 (by simp)]
  rfl

theorem size_triple {α : Type} (a b c : α) : (#[a, b, c] : Array α).size = 3 := rfl

theorem dgens_rep {l : Nat} (hl : l < 3) : CFSG.Sporadic.Th.Rep 3080 j1DGens[l]! (dG l) ∧
    CFSG.Sporadic.Th.Rep 3080 j1DGensInv[l]! (dG l)⁻¹ := by
  unfold j1DGens j1DGensInv
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
  · rw [triple0, triple0]
    exact ⟨rep_dT 0, invT_rep n32 (rep_dT 0)⟩
  · rw [triple1, triple1]
    exact ⟨rep_dT 1, invT_rep n32 (rep_dT 1)⟩
  · rw [triple2, triple2]
    exact ⟨rep_dT 2, invT_rep n32 (rep_dT 2)⟩

theorem bfsD : BfsFacts 3080 j1Chain.strongArrs j1Chain.baseArr 3 (ordK J1L.LR 3)
      (fun l g => g * dG l) 3 J1PD.c J1PD.J J1PD.PA J1PD.LB J1PD.POS ∧
    J1PD.c ≤ 200 ∧ J1PD.J 0 = J1PD.jR := by
  have hc : J1PD.c ≤ 1 * 64 := by
    have h : Nat.ble J1PD.c (1 * 64) = true := by quickRfl
    exact Nat.le_of_ble_eq_true h
  refine bfs_facts chainCK (N := ordK J1L.LR 3) (c := J1PD.c) (cap := 200) (jR := J1PD.jR)
    (ng := 3) (stp := stpM 12 (mask 12) J1W.D) (σ := fun l g => g * dG l)
    (J := J1PD.J) (PA := J1PD.PA) (LB := J1PD.LB) (POS := J1PD.POS) (SRT := J1PD.SRT)
    (SRI := J1PD.SRI) rfl ?_ J1PD.hd ?_
  · intro l hl f g hf hg
    refine ⟨fun y => ?_, Subgroup.mul_mem _ hg (dG_mem l)⟩
    unfold stpM
    rw [prep_D hl y, hf, Equiv.Perm.mul_apply]
  · have hb := elems_of_blocks hc J1PD.hb
    intro k hk
    have := hb k hk
    unfold bfsPtG at this
    rw [show Nat.blt k J1PD.c = true by rw [Nat.blt_eq]; exact hk] at this
    exact this

theorem eJ_D0 : eJ J1PD.jR = 1 := by
  have hj : J1PD.jR < ordK J1L.LR 3 := by
    rw [← bfsD.2.2]
    exact bfsD.1.lt 0 bfsD.1.c_pos
  exact (eqB_iff_eq chainCK (acts_elJ chainCK _) (fun y => rfl) (el_mem chainCK hj)
    (Subgroup.one_mem _)).1 J1PD.root

theorem replayD : KReplay 3080 (fun l y => compT 3080 y j1DGens[l]!) 3 (idT 3080)
    J1PD.c (fun k => toTable (eJ (J1PD.J k))) J1PD.PA J1PD.LB
    (fun h l => J1PD.POS (h * 3 + l)) := by
  have R := replay_of_bfs chainCK bfsD.1 rfl
    (st := fun l y => compT 3080 y j1DGens[l]!) (fun l hl k _ =>
      compT_eq_toTable n32 (rep_toTable' _) (dgens_rep hl).1)
  have e : toTable (eJ (J1PD.J 0)) = idT 3080 := by
    rw [bfsD.2.2, eJ_D0]
    exact (toTable_ext n32 (by simp [idT]) (CFSG.Sporadic.Th.Rep.idT n32)).symm
  rw [e] at R
  exact R

theorem c_D : J1PD.c = 60 := rfl

theorem dClo_eq : j1DClo = (Array.ofFn (n := J1PD.c) fun i => toTable (eJ (J1PD.J i.val)),
      Array.ofFn (n := J1PD.c) fun i => J1PD.PA i.val,
      Array.ofFn (n := J1PD.c) fun i => J1PD.LB i.val) := by
  have h := keyBfs_replay replayD bfsD.2.1
  unfold j1DClo
  rewrite [CFSG.KS.KeyBfs.mulClosure_eq, show j1DGens.size = 3 from size_triple _ _ _]
  beta_reduce at h
  exact h

theorem dElts_eq : j1DElts = Array.ofFn (n := J1PD.c) fun i => toTable (eJ (J1PD.J i.val)) := by
  rw [j1DElts_def, dClo_eq]

theorem dElts_get {k : Nat} (hk : k < J1PD.c) : j1DElts[k]! = toTable (eJ (J1PD.J k)) := by
  rw [dElts_eq, getElem!_ofFn' _ hk]

theorem dElts_size : j1DElts.size = 60 := by rw [dElts_eq, Array.size_ofFn, c_D]

theorem eD_inj {a b : Nat} (ha : a < J1PD.c) (hb : b < J1PD.c)
    (e : eJ (J1PD.J a) = eJ (J1PD.J b)) : a = b :=
  bfsD.1.inj a ha b hb (el_inj chainCK (bfsD.1.lt a ha) (bfsD.1.lt b hb) e)

theorem d_closure : mulTreeOK 3080 j1DGens j1DElts j1DClo.2.1 j1DClo.2.2 = true ∧
    mulClosedOK 3080 j1DGens j1DGensInv j1DElts = true ∧
    keysDistinct 3080 j1DElts.toList = true ∧ j1DElts.size = 60 := by
  have R := replayD
  refine ⟨?_, ?_, ?_, dElts_size⟩
  · unfold mulTreeOK
    rewrite [dElts_eq, dClo_eq]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Array.size_ofFn,
      CFSG.Sporadic.Th.allIn_eq_true]
    refine ⟨⟨R.pos_cnt, ?_⟩, fun k hk1 hk => ?_⟩
    · rw [getElem!_ofFn' _ R.pos_cnt]
      change tblEq 3080 (toTable (eJ (J1PD.J 0))) (idT 3080) = true
      rw [← R.root_eq]
      exact tblEq_refl _ _
    · obtain ⟨t1, t2, t3⟩ := R.tree k (by omega) hk
      rw [getElem!_ofFn' _ hk, getElem!_ofFn' _ hk, getElem!_ofFn' _ hk,
        getElem!_ofFn' _ (t1.trans hk)]
      refine ⟨⟨t1, t2⟩, ?_⟩
      change tblEq 3080 (toTable (eJ (J1PD.J k))) _ = true
      rw [t3]
      exact tblEq_refl _ _
  · unfold mulClosedOK
    rw [Array.all_eq_true]
    intro h hh
    rw [dElts_size] at hh
    rw [List.all_eq_true]
    intro l hl
    replace hl : l < 3 := by
      rw [List.mem_range] at hl
      exact hl
    rw [Bool.and_eq_true, Array.any_eq_true, Array.any_eq_true]
    have hh' : h < J1PD.c := by rw [c_D]; exact hh
    have hrep : CFSG.Sporadic.Th.Rep 3080 j1DElts[h] (eJ (J1PD.J h)) := by
      rw [← getElem!_pos j1DElts h (by rw [dElts_size]; exact hh), dElts_get hh']
      exact rep_toTable' _
    obtain ⟨g1, g2⟩ := dgens_rep hl
    refine ⟨?_, ?_⟩
    · obtain ⟨q1, q2, -⟩ := bfsD.1.close h hh' l hl
      refine ⟨_, by rw [dElts_size, ← c_D]; exact q1, ?_⟩
      rw [← getElem!_pos j1DElts _ (by rw [dElts_size, ← c_D]; exact q1), dElts_get q1,
        tblEq_iff_eq (rep_toTable' _) (CFSG.Sporadic.Th.Rep.compT hrep g1)]
      exact q2
    ·
      have hinj : Set.InjOn (fun h' => J1PD.POS (h' * 3 + l)) (Finset.range J1PD.c : Set Nat) :=
        fun a ha b hb e => by
          have ha' := Finset.mem_range.1 ha
          have hb' := Finset.mem_range.1 hb
          obtain ⟨-, a2, -⟩ := bfsD.1.close a ha' l hl
          obtain ⟨-, b2, -⟩ := bfsD.1.close b hb' l hl
          have a2' : eJ (J1PD.J (J1PD.POS (a * 3 + l))) = eJ (J1PD.J a) * dG l := a2
          have b2' : eJ (J1PD.J (J1PD.POS (b * 3 + l))) = eJ (J1PD.J b) * dG l := b2
          have e' : J1PD.POS (a * 3 + l) = J1PD.POS (b * 3 + l) := e
          have : eJ (J1PD.J a) * dG l = eJ (J1PD.J b) * dG l := by
            rw [← a2', ← b2', e']
          exact eD_inj ha' hb' (mul_right_cancel this)
      obtain ⟨h', hh'', e⟩ := Finset.surjOn_of_injOn_of_card_le _
        (fun a ha => Finset.mem_range.2 (bfsD.1.close a (Finset.mem_range.1 ha) l hl).1) hinj
        le_rfl (Finset.mem_coe.2 (Finset.mem_range.2 hh'))
      have hh2 := Finset.mem_range.1 hh''
      refine ⟨h', by rw [dElts_size, ← c_D]; exact hh2, ?_⟩
      obtain ⟨-, q2, -⟩ := bfsD.1.close h' hh2 l hl
      change J1PD.POS (h' * 3 + l) = h at e
      have q2' : eJ (J1PD.J (J1PD.POS (h' * 3 + l))) = eJ (J1PD.J h') * dG l := q2
      rw [e] at q2'
      rw [← getElem!_pos j1DElts _ (by rw [dElts_size, ← c_D]; exact hh2), dElts_get hh2,
        tblEq_iff_eq (rep_toTable' _) (CFSG.Sporadic.Th.Rep.compT hrep g2), q2']
      group
  · apply keysDistinct_of_nodup
    rw [dElts_eq, List.nodup_iff_injective_get]
    intro x y e
    simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList,
      Array.getElem_ofFn] at e
    have hx : x.val < J1PD.c := by simpa using x.isLt
    have hy : y.val < J1PD.c := by simpa using y.isLt
    exact Fin.ext (R.inj x hx y hy e)

theorem prodD : ∀ a < J1PD.c, (∀ b < J1PD.c, J1PD.PT (a * J1PD.c + b) < J1PD.c ∧
      eJ (J1PD.J (J1PD.PT (a * J1PD.c + b))) = eJ (J1PD.J a) * eJ (J1PD.J b)) ∧
    J1PD.INV a < J1PD.c ∧ eJ (J1PD.J a) * eJ (J1PD.J (J1PD.INV a)) = 1 :=
  prod_facts bfsD.1 (by rw [bfsD.2.2]; exact eJ_D0) fun a ha => by
    have := allN_iff.1 J1PD.hp a ha
    unfold prodPtG at this
    rw [show Nat.blt a J1PD.c = true by rw [Nat.blt_eq]; exact ha] at this
    exact this

theorem cj_spec {a i : Nat} (ha : a < J1PD.c) (hi : i < J1PD.c) :
    cjK J1PD.c J1PD.PT J1PD.INV a i < J1PD.c ∧
      eJ (J1PD.J (cjK J1PD.c J1PD.PT J1PD.INV a i)) =
        eJ (J1PD.J a) * eJ (J1PD.J i) * (eJ (J1PD.J a))⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := prodD a ha
  obtain ⟨u1, u2⟩ := h1 i hi
  obtain ⟨v1, v2⟩ := (prodD _ u1).1 (J1PD.INV a) h2
  have hinv : eJ (J1PD.J (J1PD.INV a)) = (eJ (J1PD.J a))⁻¹ := eq_inv_of_mul_eq_one_right h3
  refine ⟨v1, ?_⟩
  change eJ (J1PD.J (J1PD.PT (J1PD.PT (a * J1PD.c + i) * J1PD.c + J1PD.INV a))) = _
  rw [v2, u2, hinv]

theorem getElem!_map' {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α)
    {i : Nat} (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

theorem classes_eq : j1DClasses =
    (J1PD.REPS.toArray, J1PD.LAB.toArray, J1PD.CJ.toArray) := by
  have hl := eq_of_labOK J1PD.hl
  unfold j1DClasses
  rewrite [classLabels_eq, dElts_size, labLoop_eq]
  rewrite [← hl, show (60 : Nat) = J1PD.c from c_D.symm]
  apply labR_congr
  intro k hk c hc i hi
  have rk := dElts_get hk
  have rc := dElts_get hc
  have ri := dElts_get hi
  have hc' : c < j1DElts.size := by rw [dElts_size, ← c_D]; exact hc
  rw [getElem!_map' _ _ hc', rk, rc, ri,
    conjT_eq_toTable n32 (rep_toTable' _) (invT_rep n32 (rep_toTable' _)) (rep_toTable' _),
    Bool.eq_iff_iff, tblEq_iff_eq (rep_toTable' _) (rep_toTable' _), Nat.beq_eq]
  obtain ⟨s1, s2⟩ := cj_spec hc hi
  constructor
  · intro e
    exact eD_inj s1 hk (s2.trans e.symm)
  · intro e
    rw [← e, s2]

theorem labsK : allN 60 (fun k => Nat.blt J1PD.LAB.toArray[k]! 5 &&
    Nat.blt J1PD.CJ.toArray[k]! 60 &&
    Nat.beq (cjK J1PD.c J1PD.PT J1PD.INV J1PD.CJ.toArray[k]!
      J1PD.REPS.toArray[J1PD.LAB.toArray[k]!]!) k) = true := by
  quickRfl

theorem repsK : allN 5 (fun t => Nat.blt J1PD.REPS.toArray[t]! 60) = true := by
  quickRfl

theorem reps_size : J1PD.REPS.toArray.size = 5 := rfl

theorem reps_lt {t : Nat} (ht : t < 5) : J1PD.REPS.toArray[t]! < 60 := by
  have := allN_iff.1 repsK t ht
  rwa [Nat.blt_eq] at this

theorem d_labels : j1DClasses.1.size = 5 ∧
    classLabelsOK 3080 j1DElts j1DClasses.1 j1DClasses.2.1 j1DClasses.2.2 = true := by
  rw [classes_eq]
  refine ⟨reps_size, ?_⟩
  unfold classLabelsOK
  rw [dElts_size, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨by rw [reps_size]; decide, rfl⟩, ?_⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro t ht
    rw [reps_size] at ht
    have := reps_lt ht
    rw [getElem!_pos _ t (by rw [reps_size]; exact ht)] at this
    exact decide_eq_true this
  rw [CFSG.Sporadic.Th.allIn_eq_true]
  intro k _ hk
  have h := allN_iff.1 labsK k hk
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h4⟩ := h
  have hk' : k < J1PD.c := by rw [c_D]; exact hk
  have hc : J1PD.CJ.toArray[k]! < J1PD.c := by rw [c_D]; exact h2
  have hr : J1PD.REPS.toArray[J1PD.LAB.toArray[k]!]! < J1PD.c := by rw [c_D]; exact reps_lt h1
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, reps_size]
  refine ⟨⟨⟨decide_eq_true h1, decide_eq_true h2⟩, ?_⟩, ?_⟩
  · rw [dElts_get hc]
    exact invOK_invT n32 (rep_toTable' _)
  · rw [dElts_get hk', dElts_get hc, dElts_get hr,
      conjT_eq_toTable n32 (rep_toTable' _) (invT_rep n32 (rep_toTable' _)) (rep_toTable' _),
      tblEq_iff_eq (rep_toTable' _) (rep_toTable' _), ← (cj_spec hc hr).2, h4]

theorem subsets5 : ∀ x0 x1 x2 x3 x4 : Bool, x0 = true →
    ((List.range 60).countP fun k =>
      if h : J1PD.LAB.toArray[k]! < 5 then ![x0, x1, x2, x3, x4] ⟨J1PD.LAB.toArray[k]!, h⟩
        else false) ∣ 60 →
    ((List.range 60).countP fun k =>
      if h : J1PD.LAB.toArray[k]! < 5 then ![x0, x1, x2, x3, x4] ⟨J1PD.LAB.toArray[k]!, h⟩
        else false) = 1 ∨
    ((List.range 60).countP fun k =>
      if h : J1PD.LAB.toArray[k]! < 5 then ![x0, x1, x2, x3, x4] ⟨J1PD.LAB.toArray[k]!, h⟩
        else false) = 60 := by
  decide +kernel

theorem d_subsets : ∀ b : Fin 5 → Bool, b ⟨0, by norm_num⟩ = true →
    ((List.range 60).countP fun k =>
      if h : j1DClasses.2.1[k]! < 5 then b ⟨j1DClasses.2.1[k]!, h⟩ else false) ∣ 60 →
    ((List.range 60).countP fun k =>
      if h : j1DClasses.2.1[k]! < 5 then b ⟨j1DClasses.2.1[k]!, h⟩ else false) = 1 ∨
    ((List.range 60).countP fun k =>
      if h : j1DClasses.2.1[k]! < 5 then b ⟨j1DClasses.2.1[k]!, h⟩ else false) = 60 := by
  intro b hb
  have e : b = ![b 0, b 1, b 2, b 3, b 4] := by
    funext i
    fin_cases i <;> rfl
  rw [classes_eq, e]
  exact subsets5 _ _ _ _ _ hb

end CertificateChecks.KernelSporSch.J1

end
