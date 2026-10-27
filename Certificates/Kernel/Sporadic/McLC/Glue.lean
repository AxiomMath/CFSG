module

public import Certificates.Kernel.Sporadic.McLC.Facts
public import Certificates.Kernel.Sporadic.McLC.AlphaK
public import Certificates.Kernel.Sporadic.McLK.Final
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Certificates.Kernel.MonsterB.Co2PermSound
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLCheckInputs
public import CFSG.Certificates.Kernel.SporSch.KeySearch

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.SmallOddCore CFSG.ClassicalInvolution
open CFSG.KS.SporSch CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Co3.Native CFSG.KS.Raw

theorem perm_ext {g h : Equiv.Perm (Fin 275)} (e : ∀ x < 275, actN g x = actN h x) : g = h :=
  Equiv.ext fun x => Fin.ext (by rw [← actN_fin, ← actN_fin]; exact e x x.2)

theorem actN_inj (g : Equiv.Perm (Fin 275)) {x y : Nat} (hx : x < 275) (hy : y < 275)
    (e : actN g x = actN g y) : x = y := by
  rw [actN_of_lt _ hx, actN_of_lt _ hy] at e
  exact congrArg Fin.val (g.injective (Fin.ext e))

theorem idx_eq (g : Equiv.Perm (Fin 275)) (x : Nat) : idx 275 g x = actN g x := by
  by_cases hx : x < 275
  · rw [idx_of_lt g hx, actN_of_lt g hx]
    rfl
  · rw [idx_of_not_lt g hx]
    unfold actN
    rw [dite_eq_right hx]

theorem rep_of_actN {T : Table} {g : Equiv.Perm (Fin 275)} (h : ∀ x < 275, ap T x = actN g x) :
    Rep 275 T g := fun x hx => by rw [h x hx, idx_eq]

theorem tp_eq {T : Table} {g : Equiv.Perm (Fin 275)} (h : Rep 275 T g) : tp 275 T = g := by
  refine CFSG.Sporadic.Schreier.rep_unique (rep_tp ?_) h
  unfold CFSG.Sporadic.SmallOddCore.permOK
  apply CFSG.KC.Co2Mem.isInvA_invCand
  · intro i hi
    rw [natArr_getElem!, h i hi]
    exact idx_lt g hi
  · intro i j hi hj e
    rw [natArr_getElem!, natArr_getElem!, h i hi, h j hj, idx_of_lt _ hi, idx_of_lt _ hj] at e
    exact congrArg Fin.val (g.injective (Fin.ext e))

@[expose] noncomputable def pf (f : Nat → Nat) : Equiv.Perm (Fin 275) :=
  permOfT 275 (Array.ofFn (n := 275) fun x => UInt32.ofNat (f x.val))

theorem actN_pf {f g : Nat → Nat} (h : ∀ x < 275, f x < 275 ∧ g (f x) = x) {x : Nat}
    (hx : x < 275) : actN (pf f) x = f x := by
  have ha : ∀ y < 275, ap (Array.ofFn (n := 275) fun x => UInt32.ofNat (f x.val)) y = f y :=
    fun y hy => McLK.ap_ofFn hy (by have := (h y hy).1; omega)
  rw [actN_of_lt _ hx, pf, permOfT_val (fun y hy => by rw [ha y hy]; exact (h y hy).1)
    (fun a ha' b hb e => by rw [ha a ha', ha b hb] at e; rw [← (h a ha').2, ← (h b hb).2, e])]
  exact ha x hx

@[expose] noncomputable def wp (p : Nat → Equiv.Perm (Fin 275)) (w : List Nat) :
    Equiv.Perm (Fin 275) :=
  w.foldr (fun c acc => p c * acc) 1

theorem foldr_wp {F : Nat → Nat → Nat} {p : Nat → Equiv.Perm (Fin 275)} {w : List Nat}
    (h : ∀ c ∈ w, ∀ y < 275, F c y = actN (p c) y) {x : Nat} (hx : x < 275) :
    w.foldr F x = actN (wp p w) x := by
  induction w with
  | nil => exact (actN_one x).symm
  | cons c w ih =>
    have ih' := ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    change F c (w.foldr F x) = actN (p c * wp p w) x
    rw [actN_mul, ← ih', h c List.mem_cons_self _ (by rw [ih']; exact actN_lt _ hx)]

theorem wp_mem {S : Subgroup (Equiv.Perm (Fin 275))} {p : Nat → Equiv.Perm (Fin 275)}
    {w : List Nat} (h : ∀ c ∈ w, p c ∈ S) : wp p w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons c w ih =>
    exact S.mul_mem (h c List.mem_cons_self) (ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

theorem rep_wordTbl' {gs : List Table} {q : Nat → Equiv.Perm (Fin 275)} {w : List Nat}
    (h : ∀ l ∈ w, Rep 275 (gs.getD (l - 1) (idT 275)) (q l)) :
    Rep 275 (wordTbl 275 gs w) (wp q w) := by
  have key : ∀ (w : List Nat), (∀ l ∈ w, Rep 275 (gs.getD (l - 1) (idT 275)) (q l)) →
      ∀ (acc : Table) (a : Equiv.Perm (Fin 275)), Rep 275 acc a →
      Rep 275 (w.foldl (fun acc l => compT 275 acc (gs.getD (l - 1) (idT 275))) acc)
        (a * wp q w) := by
    intro w
    induction w with
    | nil =>
      intro _ acc a ha
      change Rep 275 acc (a * 1)
      rwa [mul_one]
    | cons l w ih =>
      intro hw acc a ha
      rw [List.foldl_cons]
      have e : a * wp q (l :: w) = a * q l * wp q w := by
        change a * (q l * wp q w) = _
        rw [mul_assoc]
      rw [e]
      exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem l hl')) _ _
        (Rep.compT ha (hw l List.mem_cons_self))
  have := key w h (idT 275) 1 (Rep.idT (by norm_num))
  rwa [one_mul] at this

@[expose] noncomputable def alP : Equiv.Perm (Fin 275) := pf (r32 McLK.AL)

@[expose] noncomputable def beP : Equiv.Perm (Fin 275) := pf (r32 McLK.BE)

theorem actN_alP {x : Nat} (hx : x < 275) : actN alP x = r32 McLK.AL x :=
  actN_pf (g := r32 McLK.AL) (fun y hy => ⟨(McLK.inv_facts hy).1, (McLK.inv_facts hy).2.1⟩) hx

theorem actN_beP {x : Nat} (hx : x < 275) : actN beP x = r32 McLK.BE x :=
  actN_pf (g := r32 McLK.BI)
    (fun y hy => ⟨(McLK.inv_facts hy).2.2.1, (McLK.inv_facts hy).2.2.2.1⟩) hx

theorem ap_Ta {x : Nat} (hx : x < 275) : ap McLData.Ta x = r32 McLK.AL x := by
  unfold McLData.Ta
  rw [McLK.orb_eq.1]
  exact McLK.al_get hx

theorem ap_Tb {x : Nat} (hx : x < 275) : ap McLData.Tb x = r32 McLK.BE x := by
  unfold McLData.Tb
  rw [McLK.orb_eq.1]
  exact McLK.be_get hx

theorem rep_Ta : Rep 275 McLData.Ta alP := rep_of_actN fun x hx => by rw [ap_Ta hx, actN_alP hx]

theorem rep_Tb : Rep 275 McLData.Tb beP := rep_of_actN fun x hx => by rw [ap_Tb hx, actN_beP hx]

theorem tp_Ta : tp 275 McLData.Ta = alP := tp_eq rep_Ta

noncomputable abbrev sg (l : Nat) : Equiv.Perm (Fin 275) := sig 275 lettersK l

theorem actN_sg {l x : Nat} (hl : l < 10) (hx : x < 275) : actN (sg l) x = LJ l x :=
  actN_sig chain_hyp hl hx

@[expose] noncomputable def qAB (l : Nat) : Equiv.Perm (Fin 275) := if l = 1 then alP else beP

@[expose] noncomputable def qK (l : Nat) : Equiv.Perm (Fin 275) := if l = 1 then sg 0 else sg 2

theorem GA_eq {l : Nat} (hl : l = 1 ∨ l = 2) {y : Nat} (hy : y < 275) :
    GA l y = actN (qAB l) y := by
  rcases hl with rfl | rfl
  · have e : qAB 1 = alP := if_pos rfl
    rw [e, actN_alP hy]
    rfl
  · have e : qAB 2 = beP := if_neg (by decide)
    rw [e, actN_beP hy]
    rfl

theorem GK_eq (l : Nat) {y : Nat} (hy : y < 275) : GK l y = actN (qK l) y := by
  by_cases h : l = 1
  · subst h
    have e : qK 1 = sg 0 := if_pos rfl
    rw [e, actN_sg (by norm_num) hy]
    rfl
  · have e : qK l = sg 2 := if_neg h
    have hb : Nat.beq l 1 = false := by
      cases h' : Nat.beq l 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') h
    rw [e, actN_sg (by norm_num) hy]
    unfold GK
    rw [hb]

theorem rep_abT {l : Nat} (hl : l = 1 ∨ l = 2) :
    Rep 275 (McLData.abT.getD (l - 1) (idT 275)) (qAB l) := by
  rcases hl with rfl | rfl
  · have e : qAB 1 = alP := if_pos rfl
    rw [e]
    exact rep_Ta
  · have e : qAB 2 = beP := if_neg (by decide)
    rw [e]
    exact rep_Tb

theorem kWords_letters : ∀ i < 2, ∀ l ∈ McLData.kWords.getD i [], l = 1 ∨ l = 2 := by
  decide

theorem kOK_spec {x : Nat} (hx : x < 275) :
    LJ 0 x = List.foldr GA x (McLData.kWords.getD 0 []) ∧
      LJ 2 x = List.foldr GA x (McLData.kWords.getD 1 []) := by
  have h0 := kOK_ok
  unfold kOK at h0
  have h := allN_spec h0 x hx
  rw [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem sg0_eq : sg 0 = wp qAB (McLData.kWords.getD 0 []) := by
  apply perm_ext
  intro x hx
  rw [actN_sg (by norm_num) hx]
  refine (kOK_spec hx).1.trans ?_
  exact foldr_wp (fun c hc y hy => GA_eq (kWords_letters 0 (by norm_num) c hc) hy) hx

theorem sg2_eq : sg 2 = wp qAB (McLData.kWords.getD 1 []) := by
  apply perm_ext
  intro x hx
  rw [actN_sg (by norm_num) hx]
  refine (kOK_spec hx).2.trans ?_
  exact foldr_wp (fun c hc y hy => GA_eq (kWords_letters 1 (by norm_num) c hc) hy) hx

theorem kx_eq : McLProof.kx = wordTbl 275 McLData.abT (McLData.kWords.getD 0 []) := rfl

theorem ky_eq : McLProof.ky = wordTbl 275 McLData.abT (McLData.kWords.getD 1 []) := rfl

theorem kgens_eq : McLData.kgens = [McLProof.kx, McLProof.ky] := rfl

theorem rep_kx : Rep 275 McLProof.kx (sg 0) := by
  rw [kx_eq, sg0_eq]
  exact rep_wordTbl' fun l hl => rep_abT (kWords_letters 0 (by norm_num) l hl)

theorem rep_ky : Rep 275 McLProof.ky (sg 2) := by
  rw [ky_eq, sg2_eq]
  exact rep_wordTbl' fun l hl => rep_abT (kWords_letters 1 (by norm_num) l hl)

theorem rep_kgens {l : Nat} (hl : l = 1 ∨ l = 2) :
    Rep 275 (McLData.kgens.getD (l - 1) (idT 275)) (qK l) := by
  rcases hl with rfl | rfl
  · have e : qK 1 = sg 0 := if_pos rfl
    rw [e, kgens_eq]
    exact rep_kx
  · have e : qK 2 = sg 2 := if_neg (by decide)
    rw [e, kgens_eq]
    exact rep_ky

noncomputable abbrev KK : Subgroup (Equiv.Perm (Fin 275)) := Subgroup.closure {sg 0, sg 2}

theorem sg0_mem : sg 0 ∈ KK := Subgroup.subset_closure (Set.mem_insert _ _)

theorem sg2_mem : sg 2 ∈ KK := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem qK_mem (l : Nat) : qK l ∈ KK := by
  unfold qK
  split_ifs
  · exact sg0_mem
  · exact sg2_mem

theorem genOf_kgens : genOf 275 McLData.kgens = KK := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ McLData.kgens.toArray := hx
    rw [kgens_eq] at hx'
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl
    · rw [tp_eq rep_kx]
      exact sg0_mem
    · rw [tp_eq rep_ky]
      exact sg2_mem
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    obtain h | h := hg
    · rw [h, ← tp_eq rep_kx]
      exact tp_mem_genOf (by rw [kgens_eq]; exact List.mem_cons_self)
    · rw [h, ← tp_eq rep_ky]
      exact tp_mem_genOf (by rw [kgens_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self)

theorem sg_inv {j : Nat} (hj : j < 5) : sg (2 * j + 1) = (sg (2 * j))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply perm_ext
  intro x hx
  rw [actN_mul, actN_one, actN_sg (by omega) hx, actN_sg (by omega) (inv_spec hj hx).1]
  exact (inv_spec hj hx).2.2

theorem sg_odd {l : Nat} (hl : l < 10) (ho : l % 2 = 1) : sg l = (sg (l - 1))⁻¹ := by
  have h := sg_inv (j := l / 2) (by omega)
  have e1 : 2 * (l / 2) + 1 = l := by omega
  have e2 : 2 * (l / 2) = l - 1 := by omega
  rw [e1, e2] at h
  exact h

theorem sg_mem4 {c : Nat} (hc : c < 4) : sg c ∈ KK := by
  interval_cases c
  · exact sg0_mem
  · rw [sg_odd (by norm_num) (by norm_num)]
    exact Subgroup.inv_mem _ sg0_mem
  · exact sg2_mem
  · rw [sg_odd (by norm_num) (by norm_num)]
    exact Subgroup.inv_mem _ sg2_mem

theorem wordOK_spec {m : Nat} (h : wordOK m = true) :
    (∀ c ∈ wordL m, c < 4) ∧ ∀ x < 275, LJ (2 * m) x = List.foldr LJ x (wordL m) := by
  unfold wordOK at h
  rw [bAnd_iff] at h
  refine ⟨fun c hc => ?_, fun x hx => Nat.eq_of_beq_eq_true (allN_spec h.2 x hx)⟩
  have h1 := List.all_eq_true.1 h.1 c hc
  rwa [Nat.blt_eq] at h1

theorem sg_word {m : Nat} (hm : m < 5) (h : wordOK m = true) : sg (2 * m) = wp sg (wordL m) := by
  obtain ⟨hc, hw⟩ := wordOK_spec h
  have hl : 2 * m < 10 := by omega
  have hlt : ∀ c ∈ wordL m, c < 10 := fun c hc' => by
    have := hc c hc'
    omega
  apply perm_ext
  intro x hx
  have e1 : actN (sg (2 * m)) x = LJ (2 * m) x := actN_sg hl hx
  have e2 : List.foldr LJ x (wordL m) = actN (wp sg (wordL m)) x :=
    foldr_wp (F := LJ) (p := sg) (w := wordL m) (fun c hc' y hy => (actN_sg (hlt c hc') hy).symm) hx
  rw [e1, hw x hx, e2]

theorem sg_even {j : Nat} (hj : j < 3) : sg (2 * (j + 2)) ∈ KK := by
  have h : wordOK (j + 2) = true := allN_spec wordOK_ok j hj
  rw [sg_word (by omega) h]
  exact wp_mem fun c hc => sg_mem4 ((wordOK_spec h).1 c hc)

theorem sg_mem {l : Nat} (hl : l < 10) : sg l ∈ KK := by
  by_cases h4 : l < 4
  · exact sg_mem4 h4
  by_cases ho : l % 2 = 0
  · have h := sg_even (j := l / 2 - 2) (by omega)
    have e : 2 * (l / 2 - 2 + 2) = l := by omega
    rwa [e] at h
  · rw [sg_odd hl (by omega)]
    have h := sg_even (j := (l - 1) / 2 - 2) (by omega)
    have e : 2 * ((l - 1) / 2 - 2 + 2) = l - 1 := by omega
    rw [e] at h
    exact Subgroup.inv_mem _ h

noncomputable abbrev gsK (j : Nat) : Equiv.Perm (Fin 275) := sg (2 * j)

theorem hrepK : ∀ j < lettersK.size / 2, Rep 275 lettersK[2 * j]! (gsK j) := by
  intro j hj
  rw [letters_get.1] at hj
  exact rep_of_actN fun x hx => by rw [letters_get.2 _ (by omega) x hx, actN_sg (by omega) hx]

theorem QK_get {t : Nat} (ht : t < 275) : QK[t]! = t := by
  unfold QK
  rw [getElem!_pos _ t (by simpa using ht)]
  simp

theorem sepK (g : Equiv.Perm (Fin 275)) (hg : ∀ t < QK.size, idx 275 g QK[t]! = QK[t]!) :
    g = 1 := by
  apply perm_ext
  intro x hx
  have h := hg x (by simpa [QK] using hx)
  rw [QK_get hx, idx_eq] at h
  rw [h, actN_one]

theorem chainK :
    (∀ i < baseK.size, TreeFacts 275 (chainTrees 275 lettersK baseK)[i]!
      (levelLetters lettersK baseK i) (pairG gsK) baseK[i]!) ∧
      (∀ i < baseK.size, ∀ g ∈ levelGroup lettersK baseK (pairG gsK) i,
        idx 275 g baseK[i]! = baseK[i]! ↔ g ∈ levelGroup lettersK baseK (pairG gsK) (i + 1)) ∧
      ∀ i ≤ baseK.size, Nat.card (levelGroup lettersK baseK (pairG gsK) i) =
        ∏ l ∈ Finset.Ico i baseK.size, (chainTrees 275 lettersK baseK)[l]!.pts.size :=
  chain_facts hrepK sepK (chain_eq.2 0)

theorem tree_size {l : Nat} (hl : l < 3) :
    ((chainTrees 275 lettersK baseK)[l]!).pts.size = CNTJ l := by
  rw [chain_eq.1, getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]
  exact pts_size (n := 275) (CNT := CNTJ) (PTS := PTSJ) (POS := POSJ) (PAR := PARJ) (LAB := LABJ) l

theorem card_level : Nat.card (levelGroup lettersK baseK (pairG gsK) 0) = 40320 := by
  rw [chainK.2.2 0 (Nat.zero_le _)]
  have hb : baseK.size = 3 := rfl
  have e : Finset.Ico 0 3 = {0, 1, 2} := by decide
  rw [hb, e, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    tree_size (by norm_num), tree_size (by norm_num), tree_size (by norm_num)]
  rfl

theorem pairG_eq {l : Nat} (hl : l < 10) : pairG gsK l = sg l := by
  unfold pairG
  split_ifs with h
  · change sg (2 * (l / 2)) = sg l
    congr 1
    omega
  · change (sg (2 * (l / 2)))⁻¹ = sg l
    rw [sg_odd hl (by omega)]
    congr 2
    omega

theorem level_eq : levelGroup lettersK baseK (pairG gsK) 0 = KK := by
  apply le_antisymm
  · unfold levelGroup lettersGroup
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l < 10 := by
      have := mem_levelLetters_zero.1 hl
      rwa [letters_get.1] at this
    rw [pairG_eq hl']
    exact sg_mem hl'
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    obtain h | h := hg
    · rw [h, ← pairG_eq (l := 0) (by norm_num)]
      exact lG_mem (mem_levelLetters_zero.2 (by rw [letters_get.1]; norm_num))
    · rw [h, ← pairG_eq (l := 2) (by norm_num)]
      exact lG_mem (mem_levelLetters_zero.2 (by rw [letters_get.1]; norm_num))

theorem card_KK : Nat.card KK = 40320 := by
  rw [← level_eq, card_level]

theorem card_K : Nat.card (genOf 275 McLData.kgens) = 40320 := by
  rw [genOf_kgens, card_KK]

noncomputable abbrev tau (i k : Nat) : Equiv.Perm (Fin 275) := twL 275 lettersK PARJ LABJ i k

theorem tau_mem {i : Nat} (hi : i < 3) : ∀ k < CNTJ i, tau i k ∈ KK := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [tau, twL, tw_eq]
    by_cases hc : 0 < k ∧ r32 (PARJ i) k < k
    · rw [if_pos hc]
      exact Subgroup.mul_mem _ (sg_mem (mem_lvK.1 (lab_mem chain_hyp hi hk hc.1)).1)
        (ih _ hc.2 (by omega))
    · rw [if_neg hc]
      exact Subgroup.one_mem _

theorem BJ_lt {j : Nat} (hj : j < 3) : BJ j < 275 := by
  interval_cases j <;> decide

theorem tau_fix {i : Nat} (hi : i < 3) : ∀ k < CNTJ i, ∀ j < i, actN (tau i k) (BJ j) = BJ j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk j hj
    rw [tau, twL, tw_eq]
    by_cases hc : 0 < k ∧ r32 (PARJ i) k < k
    · rw [if_pos hc, actN_mul]
      have e := ih _ hc.2 (by omega) j hj
      rw [tau, twL] at e
      have hl := mem_lvK.1 (lab_mem chain_hyp hi hk hc.1)
      rw [e, actN_sig chain_hyp hl.1 (BJ_lt (by omega))]
      exact hl.2 j hj
    · rw [if_neg hc, actN_one]

theorem tau_pt {i : Nat} (hi : i < 3) {k : Nat} (hk : k < CNTJ i) :
    actN (tau i k) (BJ i) = r32 (PTSJ i) k :=
  tw_pt chain_hyp hi k hk

theorem pts_inj {i : Nat} (hi : i < 3) {a b : Nat} (ha : a < CNTJ i) (hb : b < CNTJ i)
    (e : r32 (PTSJ i) a = r32 (PTSJ i) b) : a = b :=
  (rep_of chain_hyp hi).inj ha hb e

theorem TT_spec {i k : Nat} (hi : i < 3) (hk : k < CNTJ i) {x : Nat} (hx : x < 275) :
    pk (TT i k) x = actN (tau i k) x ∧ pk (TTI i k) (pk (TT i k) x) = x := by
  have h0 := trAll_ok
  unfold trAll at h0
  have h := allN_spec (allN_spec h0 i hi) k hk
  unfold trOK at h
  simp only [strictB_eq, bAnd_iff, listEqK_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hw := walkF_eq chain_hyp hi k k hk (Nat.le_refl _) QL (fun y hy => by simpa [QL] using hy)
  have hm : x ∈ QL := by simpa [QL] using hx
  unfold walkK at h1
  rw [hw] at h1
  exact ⟨(List.map_inj_left.1 h1 x hm).symm, Nat.eq_of_beq_eq_true (allN_spec h2 x hx)⟩

theorem TTI_spec {i k : Nat} (hi : i < 3) (hk : k < CNTJ i) {y : Nat} (hy : y < 275) :
    pk (TTI i k) y = actN (tau i k)⁻¹ y := by
  have hx := actN_lt (tau i k)⁻¹ hy
  have e : pk (TT i k) (actN (tau i k)⁻¹ y) = y := by
    rw [(TT_spec hi hk hx).1, ← actN_mul, mul_inv_cancel, actN_one]
  have := (TT_spec hi hk hx).2
  rw [e] at this
  exact this

@[expose] noncomputable def X3 (a b c : Nat) : Equiv.Perm (Fin 275) := tau 0 a * tau 1 b * tau 2 c

@[expose] noncomputable def Xt (t : Nat) : Equiv.Perm (Fin 275) := X3 (t / 168) (t / 3 % 56) (t % 3)

theorem X3_mem {a b c : Nat} (ha : a < 240) (hb : b < 56) (hc : c < 3) : X3 a b c ∈ KK :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (tau_mem (by norm_num) a ha) (tau_mem (by norm_num) b hb))
    (tau_mem (by norm_num) c hc)

theorem X3_base {a b c : Nat} (hb : b < 56) (hc : c < 3) :
    actN (X3 a b c) 0 = actN (tau 0 a) 0 ∧ actN (X3 a b c) 14 = actN (tau 0 a) (r32 (PTSJ 1) b) ∧
      actN (X3 a b c) 2 = actN (tau 0 a) (actN (tau 1 b) (r32 (PTSJ 2) c)) := by
  unfold X3
  simp only [actN_mul]
  have f20 := tau_fix (i := 2) (by norm_num) c hc 0 (by norm_num)
  have f21 := tau_fix (i := 2) (by norm_num) c hc 1 (by norm_num)
  have f10 := tau_fix (i := 1) (by norm_num) b hb 0 (by norm_num)
  have p1 := tau_pt (i := 1) (by norm_num) hb
  have p2 := tau_pt (i := 2) (by norm_num) hc
  have b0 : BJ 0 = 0 := rfl
  have b1 : BJ 1 = 14 := rfl
  have b2 : BJ 2 = 2 := rfl
  rw [b0] at f20 f10
  rw [b1] at f21 p1
  rw [b2] at p2
  rw [f20, f10, f21, p1, p2]
  exact ⟨rfl, rfl, rfl⟩

theorem coords_eq {a b c a' b' c' : Nat} (ha : a < 240) (hb : b < 56) (hc : c < 3)
    (ha' : a' < 240) (hb' : b' < 56) (hc' : c' < 3)
    (e0 : actN (X3 a b c) 0 = actN (X3 a' b' c') 0)
    (e1 : actN (X3 a b c) 14 = actN (X3 a' b' c') 14)
    (e2 : actN (X3 a b c) 2 = actN (X3 a' b' c') 2) : a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨u0, u1, u2⟩ := X3_base (a := a) hb hc
  obtain ⟨v0, v1, v2⟩ := X3_base (a := a') hb' hc'
  have p0 := tau_pt (i := 0) (by norm_num) (k := a) ha
  have p0' := tau_pt (i := 0) (by norm_num) (k := a') ha'
  have b0 : BJ 0 = 0 := rfl
  rw [b0] at p0 p0'
  rw [u0, v0, p0, p0'] at e0
  have hA : a = a' := pts_inj (i := 0) (by norm_num) ha ha' e0
  subst hA
  have l1 : ∀ k < 56, r32 (PTSJ 1) k < 275 := fun k hk => by
    rw [← tau_pt (i := 1) (by norm_num) hk]
    exact actN_lt _ (BJ_lt (by norm_num))
  have l2 : ∀ k < 3, r32 (PTSJ 2) k < 275 := fun k hk => by
    rw [← tau_pt (i := 2) (by norm_num) hk]
    exact actN_lt _ (BJ_lt (by norm_num))
  rw [u1, v1] at e1
  have hB : b = b' := pts_inj (i := 1) (by norm_num) hb hb' (actN_inj _ (l1 b hb) (l1 b' hb') e1)
  subst hB
  rw [u2, v2] at e2
  have e2' := actN_inj _ (actN_lt _ (l2 c hc)) (actN_lt _ (l2 c' hc')) e2
  have hC : c = c' := pts_inj (i := 2) (by norm_num) hc hc' (actN_inj _ (l2 c hc) (l2 c' hc') e2')
  exact ⟨rfl, rfl, hC⟩

theorem Xt_mem {t : Nat} (ht : t < 40320) : Xt t ∈ KK :=
  X3_mem (by omega) (by omega) (by omega)

theorem Xt_coords {t t' : Nat} (ht : t < 40320) (ht' : t' < 40320)
    (e0 : actN (Xt t) 0 = actN (Xt t') 0) (e1 : actN (Xt t) 14 = actN (Xt t') 14)
    (e2 : actN (Xt t) 2 = actN (Xt t') 2) : t = t' := by
  obtain ⟨h1, h2, h3⟩ := coords_eq (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) e0 e1 e2
  omega

theorem exists_coords {g : Equiv.Perm (Fin 275)} (hg : g ∈ KK) : ∃ t < 40320, Xt t = g := by
  classical
  have hS : ((Finset.range 40320).image Xt).card = 40320 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro t ht t' ht' e
    simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
    exact Xt_coords ht ht' (by rw [e]) (by rw [e]) (by rw [e])
  have hsub : (((Finset.range 40320).image Xt : Finset (Equiv.Perm (Fin 275))) :
      Set (Equiv.Perm (Fin 275))) ⊆ (KK : Set (Equiv.Perm (Fin 275))) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
    exact Xt_mem (Finset.mem_range.1 ht)
  have h1 : (KK : Set (Equiv.Perm (Fin 275))).ncard = 40320 := by
    rw [← Nat.card_coe_set_eq]
    exact card_KK
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [h1, Set.ncard_coe_finset, hS])
    (Set.toFinite _)
  have hm : g ∈ (((Finset.range 40320).image Xt : Finset (Equiv.Perm (Fin 275))) :
      Set (Equiv.Perm (Fin 275))) := by
    rw [heq]
    exact hg
  obtain ⟨t, ht, e⟩ := Finset.mem_image.1 hm
  exact ⟨t, Finset.mem_range.1 ht, e⟩

theorem eq_of_base {g h : Equiv.Perm (Fin 275)} (hg : g ∈ KK) (hh : h ∈ KK)
    (e0 : actN g 0 = actN h 0) (e1 : actN g 14 = actN h 14) (e2 : actN g 2 = actN h 2) : g = h := by
  obtain ⟨t, ht, rfl⟩ := exists_coords hg
  obtain ⟨t', ht', rfl⟩ := exists_coords hh
  rw [Xt_coords ht ht' e0 e1 e2]

theorem alP_mem : alP ∈ KK := by
  have e : alP = wp qK [1, 1, 1, 1, 1, 1, 1] := by
    apply perm_ext
    intro x hx
    have h0 := alOK_ok
    unfold alOK at h0
    rw [actN_alP hx]
    refine (Nat.eq_of_beq_eq_true (allN_spec h0 x hx)).trans ?_
    exact foldr_wp (fun c _ y hy => GK_eq c hy) hx
  rw [e]
  exact wp_mem fun c _ => qK_mem c

@[expose] noncomputable def rho (j : Nat) : Equiv.Perm (Fin 275) := wp qK (repD j).1

theorem rho_mem (j : Nat) : rho j ∈ KK := wp_mem fun c _ => qK_mem c

theorem RP_spec {j : Nat} (hj : j < 21) {x : Nat} (hx : x < 275) :
    pk (RP j) x = actN (rho j) x := by
  have h0 := repOK_ok
  unfold repOK at h0
  have h := allN_spec h0 j hj
  rw [strictB_eq] at h
  refine (Nat.eq_of_beq_eq_true (allN_spec h x hx)).trans ?_
  exact foldr_wp (fun c _ y hy => GK_eq c hy) hx

theorem repData_len : McLData.repData.length = 21 := by decide

theorem repData_letters : ∀ j < 21, (∀ l ∈ (repD j).1, l = 1 ∨ l = 2) ∧
    ∀ cw ∈ (repD j).2, ∀ l ∈ cw, l = 1 ∨ l = 2 := by
  decide +kernel

theorem rep_word_kgens {w : List Nat} (hw : ∀ l ∈ w, l = 1 ∨ l = 2) :
    Rep 275 (wordTbl 275 McLData.kgens w) (wp qK w) :=
  rep_wordTbl' fun l hl => rep_kgens (hw l hl)

theorem rho_rep {j : Nat} (hj : j < 21) :
    rho j ∈ McLData.repTbls.map (tp 275) := by
  refine List.mem_map.2 ⟨wordTbl 275 McLData.kgens (repD j).1, ?_,
    tp_eq (rep_word_kgens (repData_letters j hj).1)⟩
  refine List.mem_map.2 ⟨repD j, ?_, rfl⟩
  unfold repD
  rw [List.getD_eq_getElem _ _ (by rw [repData_len]; exact hj)]
  exact List.getElem_mem _

theorem prod3_X {t : Nat} (ht : t < 40320) {y : Nat} (hy : y < 275) :
    prod3 (T0 (Nat.div t 168)) (T1 (Nat.mod (Nat.div t 3) 56)) (T2 (Nat.mod t 3)) y =
      actN (Xt t) y := by
  change pk (TT 0 (t / 168)) (pk (TT 1 (t / 3 % 56)) (pk (TT 2 (t % 3)) y)) = _
  have h2 := (TT_spec (i := 2) (k := t % 3) (by norm_num) (by change t % 3 < 3; omega) hy).1
  rw [h2]
  have h1 := (TT_spec (i := 1) (k := t / 3 % 56) (by norm_num) (by change t / 3 % 56 < 56; omega)
    (actN_lt (tau 2 (t % 3)) hy)).1
  rw [h1]
  have h0 := (TT_spec (i := 0) (k := t / 168) (by norm_num) (by change t / 168 < 240; omega)
    (actN_lt (tau 1 (t / 3 % 56)) (actN_lt (tau 2 (t % 3)) hy))).1
  rw [h0]
  unfold Xt X3
  simp only [actN_mul]

theorem prod3_I {c0 c1 c2 : Nat} (h0 : c0 < 240) (h1 : c1 < 56) (h2 : c2 < 3) {y : Nat}
    (hy : y < 275) : prod3 (T2I c2) (T1I c1) (T0I c0) y = actN (X3 c0 c1 c2)⁻¹ y := by
  change pk (TTI 2 c2) (pk (TTI 1 c1) (pk (TTI 0 c0) y)) = _
  rw [TTI_spec (i := 0) (by norm_num) h0 hy,
    TTI_spec (i := 1) (by norm_num) h1 (actN_lt (tau 0 c0)⁻¹ hy),
    TTI_spec (i := 2) (by norm_num) h2 (actN_lt (tau 1 c1)⁻¹ (actN_lt (tau 0 c0)⁻¹ hy))]
  unfold X3
  simp only [mul_inv_rev, actN_mul]

theorem bIf_iff (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = true ↔ (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp

theorem z0 : (0 : Nat) < 275 := by norm_num

theorem z14 : (14 : Nat) < 275 := by norm_num

theorem z2 : (2 : Nat) < 275 := by norm_num

theorem conj_base {t j c0 c1 c2 y : Nat} (ht : t < 40320) (hj : j < 21) (hc0 : c0 < 240)
    (hc1 : c1 < 56) (hc2 : c2 < 3) (hy : y < 275)
    (a : prod3 (T2I c2) (T1I c1) (T0I c0)
        (prod3 (T0 (Nat.div t 168)) (T1 (Nat.mod (Nat.div t 3) 56)) (T2 (Nat.mod t 3)) y) =
      pk (RP j) (prod3 (T2I c2) (T1I c1) (T0I c0) y)) :
    actN ((X3 c0 c1 c2)⁻¹ * Xt t) y = actN (rho j * (X3 c0 c1 c2)⁻¹) y := by
  rw [prod3_X ht hy, prod3_I hc0 hc1 hc2 (actN_lt (Xt t) hy), prod3_I hc0 hc1 hc2 hy,
    RP_spec hj (actN_lt (X3 c0 c1 c2)⁻¹ hy)] at a
  rw [actN_mul, actN_mul]
  exact a

theorem conj_case {t j c0 c1 c2 : Nat} (ht : t < 40320) (hj : j < 21) (hc0 : c0 < 240)
    (hc1 : c1 < 56) (hc2 : c2 < 3)
    (a0 : prod3 (T2I c2) (T1I c1) (T0I c0)
        (prod3 (T0 (Nat.div t 168)) (T1 (Nat.mod (Nat.div t 3) 56)) (T2 (Nat.mod t 3)) 0) =
      pk (RP j) (prod3 (T2I c2) (T1I c1) (T0I c0) 0))
    (a1 : prod3 (T2I c2) (T1I c1) (T0I c0)
        (prod3 (T0 (Nat.div t 168)) (T1 (Nat.mod (Nat.div t 3) 56)) (T2 (Nat.mod t 3)) 14) =
      pk (RP j) (prod3 (T2I c2) (T1I c1) (T0I c0) 14))
    (a2 : prod3 (T2I c2) (T1I c1) (T0I c0)
        (prod3 (T0 (Nat.div t 168)) (T1 (Nat.mod (Nat.div t 3) 56)) (T2 (Nat.mod t 3)) 2) =
      pk (RP j) (prod3 (T2I c2) (T1I c1) (T0I c0) 2)) :
    Xt t = X3 c0 c1 c2 * rho j * (X3 c0 c1 c2)⁻¹ := by
  have hX := X3_mem hc0 hc1 hc2
  have key : (X3 c0 c1 c2)⁻¹ * Xt t = rho j * (X3 c0 c1 c2)⁻¹ :=
    eq_of_base (Subgroup.mul_mem _ (Subgroup.inv_mem _ hX) (Xt_mem ht))
      (Subgroup.mul_mem _ (rho_mem _) (Subgroup.inv_mem _ hX))
      (conj_base ht hj hc0 hc1 hc2 z0 a0) (conj_base ht hj hc0 hc1 hc2 z14 a1)
      (conj_base ht hj hc0 hc1 hc2 z2 a2)
  calc Xt t = X3 c0 c1 c2 * ((X3 c0 c1 c2)⁻¹ * Xt t) := by group
    _ = X3 c0 c1 c2 * (rho j * (X3 c0 c1 c2)⁻¹) := by rw [key]
    _ = X3 c0 c1 c2 * rho j * (X3 c0 c1 c2)⁻¹ := by group

theorem cover_at {t : Nat} (ht : t < 40320) :
    Xt t = 1 ∨ Xt t = alP ∨ ∃ j < 21, ∃ c ∈ KK, Xt t = c * rho j * c⁻¹ := by
  have h := cover_all t ht
  unfold coverW at h
  simp only [strictB_eq] at h
  generalize r32 WT t = w at h
  rcases (bIf_iff _ _ _).1 h with ⟨-, hA⟩ | ⟨-, h⟩
  · left
    simp only [bAnd_iff, Nat.beq_eq] at hA
    obtain ⟨a0, a1, a2⟩ := hA
    rw [prod3_X ht z0] at a0
    rw [prod3_X ht z14] at a1
    rw [prod3_X ht z2] at a2
    exact eq_of_base (Xt_mem ht) (Subgroup.one_mem _) (by rw [a0, actN_one]) (by rw [a1, actN_one])
      (by rw [a2, actN_one])
  rcases (bIf_iff _ _ _).1 h with ⟨-, hA⟩ | ⟨-, h⟩
  · right
    left
    simp only [bAnd_iff, Nat.beq_eq] at hA
    obtain ⟨a0, a1, a2⟩ := hA
    rw [prod3_X ht z0] at a0
    rw [prod3_X ht z14] at a1
    rw [prod3_X ht z2] at a2
    exact eq_of_base (Xt_mem ht) alP_mem (by rw [a0, actN_alP z0]) (by rw [a1, actN_alP z14])
      (by rw [a2, actN_alP z2])
  right
  right
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hj, hc0, hc1, hc2, a0, a1, a2⟩ := h
  exact ⟨_, hj, _, X3_mem hc0 hc1 hc2, conj_case ht hj hc0 hc1 hc2 a0 a1 a2⟩

theorem cover_K : ∀ x ∈ genOf 275 McLData.kgens, x = 1 ∨ x = tp 275 McLData.Ta ∨
    ∃ r ∈ McLData.repTbls.map (tp 275), ∃ c ∈ genOf 275 McLData.kgens, x = c * r * c⁻¹ := by
  intro x hx
  rw [genOf_kgens] at hx ⊢
  rw [tp_Ta]
  obtain ⟨t, ht, rfl⟩ := exists_coords hx
  rcases cover_at ht with h | h | ⟨j, hj, c, hc, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨rho j, rho_rep hj, c, hc, h⟩)

end CertificateChecks.KernelSpor.McLC

end
