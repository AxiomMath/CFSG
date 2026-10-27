module

public import Certificates.Kernel.HN1408.FixRFacts
public import Certificates.Kernel.HN1408.FixRPt
public import Certificates.Kernel.HN1408.FixRChk3
public import Certificates.Kernel.HN1408.FixRChk5a
public import Certificates.Kernel.HN1408.FixRChk5b0
public import Certificates.Kernel.HN1408.FixRChk5b1
public import Certificates.Kernel.HN1408.FixRChk5c
public import Certificates.Kernel.HN1408.FixRChk7
public import Certificates.Kernel.HN1408.FixRYIChk
public import Certificates.Kernel.HN1408.FctChk
public import Certificates.Kernel.HN1408.Tr2Facts
public import Certificates.Kernel.HN1408.TransFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixClass
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.FixR

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.KD.HN1408.Tr2 (Tr2OK genC)

#kc_forall_chunks f3_rep_all (fun s => FixR.f3Rep s = true) 5 CFSG.KD.HN1408.ch26775f3.rep 1
#kc_forall_chunks f3_srt_all (fun s => FixR.f3Sort s = true) 2 CFSG.KD.HN1408.ch26775f3.srt 1
#kc_forall_chunks f5a_rep_all (fun s => FixR.f5aRep s = true) 2 CFSG.KD.HN1408.ch26775f5a.rep 1
#kc_forall_chunks f5a_srt_all (fun s => FixR.f5aSort s = true) 1 CFSG.KD.HN1408.ch26775f5a.srt 1
#kc_forall_chunks f5b_rep_all (fun s => FixR.f5bRep s = true) 34 CFSG.KD.HN1408.ch26775f5b.rep 1
#kc_forall_chunks f5b_srt_all (fun s => FixR.f5bSort s = true) 5 CFSG.KD.HN1408.ch26775f5b.srt 1
#kc_forall_chunks f5c_rep_all (fun s => FixR.f5cRep s = true) 8 CFSG.KD.HN1408.ch26775f5c.rep 1
#kc_forall_chunks f5c_srt_all (fun s => FixR.f5cSort s = true) 3 CFSG.KD.HN1408.ch26775f5c.srt 1
#kc_forall_chunks f7_rep_all (fun s => FixR.f7Rep s = true) 3 CFSG.KD.HN1408.ch26775f7.rep 1
#kc_forall_chunks f7_srt_all (fun s => FixR.f7Sort s = true) 17 CFSG.KD.HN1408.ch26775f7.srt 1

theorem fixCnt_rec {X : Nat} : ∀ n, Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc (nIf(Nat.beq (pt X i) i, 1, 0))) n =
      ((Finset.range n).filter fun i => pt X i = i).card
  | 0 => rfl
  | n + 1 => by
    have ih := fixCnt_rec (X := X) n
    change Nat.add (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.add acc (nIf(Nat.beq (pt X i) i, 1, 0))) n)
        (nIf(Nat.beq (pt X n) n, 1, 0)) = _
    rw [ih, nIf_ite, Finset.range_add_one, Finset.filter_insert]
    by_cases h : pt X n = n
    · rw [if_pos (by simp [h]), if_pos h, Finset.card_insert_of_notMem
        (fun hm => by simp at hm)]
    · rw [if_neg (fun h' => h (Nat.eq_of_beq_eq_true h')), if_neg h]
      rfl

theorem fixCntF_eq {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) :
    fixCntF X = (Finset.univ.filter fun p : Fin 1408 => g p = p).card := by
  unfold fixCntF
  rw [fixCnt_rec, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨hi, e⟩
    refine ⟨⟨i, hi⟩, Fin.ext ?_, rfl⟩
    rw [← repC_pt hX hi, e]
  · rintro ⟨p, e, rfl⟩
    refine ⟨p.2, ?_⟩
    rw [repC_pt hX p.2]
    exact congrArg Fin.val e

theorem slice_index {i n len ns : Nat} (hi : i < n) (hn : n ≤ len * ns) :
    0 < len ∧ i / len < ns ∧ Nat.add (Nat.mul len (i / len)) (i % len) = i := by
  have hlen : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | h0
    · subst h0
      omega
    · exact h0
  refine ⟨hlen, Nat.div_lt_of_lt_mul (by omega), ?_⟩
  simp only [Nat.add_eq, Nat.mul_eq]
  exact Nat.div_add_mod i len

theorem repFSl_all {G GI Y YI R P : Nat → Nat} {nG nY n len ns : Nat} (hn : n ≤ len * ns)
    (h : ∀ s < ns, repFSl G GI Y YI R P nG nY n (Nat.mul len s) len = true) :
    ∀ i < n, 0 < i → repF G GI Y YI R P nG nY i = true := by
  intro i hi hpos
  obtain ⟨hlen, hs, e⟩ := slice_index hi hn
  have h' := allN_spec (h _ hs) (i % len) (Nat.mod_lt _ hlen)
  simp only [strictB_app] at h'
  rw [e, Nat.blt_eq.mpr hi] at h'
  have e0 : Nat.beq i 0 = false :=
    Bool.eq_false_iff.2 fun h'' => by have := Nat.eq_of_beq_eq_true h''; omega
  rw [e0] at h'
  exact h'

theorem sortFSl_all {Y YI R S : Nat → Nat} {nY n cnt len ns : Nat} (hn : cnt ≤ len * ns)
    (h : ∀ s < ns, sortFSl Y YI R S nY n cnt (Nat.mul len s) len = true) :
    ∀ m < cnt, sortFAt Y YI R S nY n cnt m = true := by
  intro m hm
  obtain ⟨hlen, hs, e⟩ := slice_index hm hn
  have h' := allN_spec (h _ hs) (m % len) (Nat.mod_lt _ hlen)
  simp only [strictB_app] at h'
  rw [e, Nat.blt_eq.mpr hm] at h'
  exact h'

abbrev RecFacts (w : List Nat) (fix nY n cnt : Nat) (Y YI R : Nat → Nat) : Prop :=
  (∃ M : Finset (Equiv.Perm (Fin 1408)), M.card = cnt ∧
      ∀ z ∈ M, z ∈ conjClass P1408 (elemW w) ∧ z ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩) ∧
    (Finset.univ.filter fun p : Fin 1408 => elemW w p = p).card = fix ∧
    ∀ i < n, ∀ j < nY, ∀ g, RepC (cyF Y YI j (R i)) g → g ∈ conjClass P1408 (elemW w)

theorem class_count {ws yws : List (List Nat)} {w : List Nat} {fix nY n cnt : Nat}
    {G GI YG Y YI YP R P S : Nat → Nat}
    (hlw : ∀ j < ws.length, lettersOK (ws.getD j []) = true)
    (hly : ∀ l < yws.length, lettersOK (yws.getD l []) = true) (hw : lettersOK w = true)
    (hhead : headF ws yws w fix nY G GI YG Y YI YP R = true) (hyi : yInvF Y YI nY = true)
    (h0 : Nat.beq (pt (R 0) 0) 0 = true)
    (hr : ∀ i < n, 0 < i → repF G GI Y YI R P ws.length nY i = true)
    (hs : ∀ m < cnt, sortFAt Y YI R S nY n cnt m = true) : RecFacts w fix nY n cnt Y YI R := by
  unfold headF at hhead
  obtain ⟨hg, hhead⟩ := mkA hhead
  obtain ⟨hyg, hhead⟩ := mkA hhead
  obtain ⟨hyt, hhead⟩ := mkA hhead
  obtain ⟨hR0, hfix⟩ := mkA hhead
  have hRw : RepC (R 0) (elemW w) := by
    rw [Nat.eq_of_beq_eq_true hR0]
    exact repC_word hw
  have hx0 : elemW w ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
    Fin.ext (by rw [← repC_pt hRw (by norm_num)]; exact Nat.eq_of_beq_eq_true h0)
  have hY := yTree_parts hly hyg hyt hyi
  have hreps := reps_memF (gHead_parts hlw hg) hY hRw hx0 hr
  refine ⟨count_geF hY hreps hs, ?_, fun i hi j hj g hg => ?_⟩
  · rw [← fixCntF_eq hRw]
    exact Nat.eq_of_beq_eq_true hfix
  · obtain ⟨c, hcP, hc, -⟩ := hreps i hi
    obtain ⟨y, hyP, hyR, hyiR, -⟩ := hY j hj
    have e := eq_of_repC hg (repC_pc (repC_pc hyR hc) hyiR)
    refine ⟨y * c, mul_mem hyP hcP, ?_⟩
    rw [e]
    group

theorem cent_exact (hP : Nat.card ↥P1408 = 177408000) {x : Equiv.Perm (Fin 1408)}
    (hx : x ∈ P1408) {H : Subgroup (Equiv.Perm (Fin 1408))}
    (hH : H ≤ P1408 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1408)))) {L m f : Nat}
    (hL : L ≤ Nat.card H)
    (hM : ∃ M : Finset (Equiv.Perm (Fin 1408)), M.card = m ∧
      ∀ z ∈ M, z ∈ conjClass P1408 x ∧ z ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩)
    (hf : (Finset.univ.filter fun p : Fin 1408 => x p = p).card = f)
    (harith : 177408000 * f = L * (1408 * m)) (hm : 0 < m) :
    Nat.card ↥(P1408 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1408)))) = L ∧
      H = P1408 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1408))) := by
  obtain ⟨M, hMc, hMf⟩ := hM
  have h1 := TwoHSData.card_centralizer_mul_le P1408 ⟨0, by norm_num⟩ Trans.trans_K hx M hMf
  rw [hP, hf, hMc, harith] at h1
  have h2 := Nat.le_of_mul_le_mul_right h1 (by omega)
  have h3 := Subgroup.card_le_of_le hH
  exact ⟨by omega, Subgroup.eq_of_le_of_card_ge hH (by omega)⟩

theorem fct3_ok : Tr2OK fix3.cent fix3.rep 40 36 3 Fct3.G Fct3.T0 Fct3.P0 Fct3.S Fct3.SR
    Fct3.T1 Fct3.P1 where
  letters l hl := by
    have hl' : l < 4 := hl
    interval_cases l <;> decide
  zw := by decide
  head := fct3_head
  keys := fct3_keys
  tree := fct3_tree
  sch := fct3_sch
  t1 := fct3_t1

theorem fct5a_ok : Tr2OK cent5aW rep5aW 1000 2 1 Fct5a.G Fct5a.T0 Fct5a.P0 Fct5a.S Fct5a.SR
    Fct5a.T1 Fct5a.P1 where
  letters l hl := by
    have hl' : l < 4 := hl
    interval_cases l <;> decide
  zw := by decide
  head := fct5a_head
  keys := fct5a_keys
  tree := allN_intro fun i hi => by
    rcases Nat.lt_or_ge i 500 with h | h
    · exact allN_spec fct5a_tree0 i h
    · have e := allN_spec fct5a_tree1 (i - 500) (by omega)
      have e2 : Nat.add 500 (i - 500) = i := by
        simp only [Nat.add_eq]
        omega
      rw [e2] at e
      exact e
  sch := fct5a_sch
  t1 := fct5a_t1

theorem fct5b_ok : Tr2OK fix5B.cent fix5B.rep 4 25 2 Fct5b.G Fct5b.T0 Fct5b.P0 Fct5b.S Fct5b.SR
    Fct5b.T1 Fct5b.P1 where
  letters l hl := by
    have hl' : l < 2 := hl
    interval_cases l <;> decide
  zw := by decide
  head := fct5b_head
  keys := fct5b_keys
  tree := fct5b_tree
  sch := fct5b_sch
  t1 := fct5b_t1

theorem fct5c_ok : Tr2OK fix5C.cent fix5C.rep 48 25 2 Fct5c.G Fct5c.T0 Fct5c.P0 Fct5c.S Fct5c.SR
    Fct5c.T1 Fct5c.P1 where
  letters l hl := by
    have hl' : l < 3 := hl
    interval_cases l <;> decide
  zw := by decide
  head := fct5c_head
  keys := fct5c_keys
  tree := fct5c_tree
  sch := fct5c_sch
  t1 := fct5c_t1

theorem fct7_ok : Tr2OK fix7.cent fix7.rep 4 7 1 Fct7.G Fct7.T0 Fct7.P0 Fct7.S Fct7.SR
    Fct7.T1 Fct7.P1 where
  letters l hl := by
    have hl' : l < 2 := hl
    interval_cases l <;> decide
  zw := by decide
  head := fct7_head
  keys := fct7_keys
  tree := fct7_tree
  sch := fct7_sch
  t1 := fct7_t1

theorem cw0_letters : ∀ j < cw0.length, lettersOK (cw0.getD j []) = true := by
  intro j hj
  have hj' : j < 2 := hj
  interval_cases j <;> decide

theorem cw5b_letters : ∀ j < cw5b.length, lettersOK (cw5b.getD j []) = true := by
  intro j hj
  have hj' : j < 3 := hj
  interval_cases j <;> decide

theorem cw7_letters : ∀ j < cw7.length, lettersOK (cw7.getD j []) = true := by
  intro j hj
  have hj' : j < 3 := hj
  interval_cases j <;> decide

theorem yw7_letters : ∀ l < yw7.length, lettersOK (yw7.getD l []) = true := by
  intro l hl
  have hl' : l < 1 := hl
  interval_cases l
  decide

theorem yw3_letters : ∀ l < yw3.length, lettersOK (yw3.getD l []) = true := by
  intro l hl
  have hl' : l < 1 := hl
  interval_cases l
  decide

theorem syl5_letters : ∀ l < sylow5Words.length, lettersOK (sylow5Words.getD l []) = true := by
  intro l hl
  have hl' : l < 3 := hl
  interval_cases l <;> decide

abbrev CentFacts (d : FixData) : Prop :=
  Nat.card ↥(P1408 ⊓ centralizer ({elemW d.rep} : Set (Equiv.Perm (Fin 1408)))) = d.centOrder ∧
    genC d.cent = P1408 ⊓ centralizer ({elemW d.rep} : Set (Equiv.Perm (Fin 1408)))

theorem rec3 : RecFacts fix3.rep fix3.fix 7 500 3500 Fix3.Y Fix3.YI Fix3.R := by
  have hh : headF cw0 yw7 fix3.rep fix3.fix 7 Fix3.G Fix3.GI Fix3.YG Fix3.Y Fix3.YI Fix3.YP
      Fix3.R = true := f3_head
  exact class_count (P := Fix3.P) (S := Fix3.S) cw0_letters
    yw7_letters (by decide) hh f3_yinv f3_pt0
    (repFSl_all (len := 100) (ns := 5) (by norm_num) fun s hs => by
      have h := f3_rep_all s hs
      unfold f3Rep at h
      exact h)
    (sortFSl_all (len := 2200) (ns := 2) (by norm_num) fun s hs => by
      have h := f3_srt_all s hs
      unfold f3Sort at h
      exact h)

theorem cent3_facts (hP : Nat.card ↥P1408 = 177408000) : CentFacts fix3 :=
  cent_exact hP (elemW_mem _) (Tr2.le_cent fct3_ok) (Tr2.card_ge fct3_ok) rec3.1 rec3.2.1
    (by decide) (by norm_num)

theorem rec5b : RecFacts fix5B.rep fix5B.fix 3 3360 10080 Fix5b.Y Fix5b.YI Fix5b.R := by
  have hh : headF cw5b yw3 fix5B.rep fix5B.fix 3 Fix5b.G Fix5b.GI Fix5b.YG Fix5b.Y Fix5b.YI
      Fix5b.YP Fix5b.R = true := f5b_head
  exact class_count (P := Fix5b.P) (S := Fix5b.S) cw5b_letters
    yw3_letters (by decide) hh f5b_yinv f5b_pt0
    (repFSl_all (len := 100) (ns := 34) (by norm_num) fun s hs => by
      have h := f5b_rep_all s hs
      unfold f5bRep at h
      exact h)
    (sortFSl_all (len := 2200) (ns := 5) (by norm_num) fun s hs => by
      have h := f5b_srt_all s hs
      unfold f5bSort at h
      exact h)

theorem cent5b_facts (hP : Nat.card ↥P1408 = 177408000) : CentFacts fix5B :=
  cent_exact hP (elemW_mem _) (Tr2.le_cent fct5b_ok) (Tr2.card_ge fct5b_ok) rec5b.1 rec5b.2.1
    (by decide) (by norm_num)

theorem rec5c : RecFacts fix5C.rep fix5C.fix 7 720 5040 Fix5c.Y Fix5c.YI Fix5c.R := by
  have hh : headF cw0 yw7 fix5C.rep fix5C.fix 7 Fix5c.G Fix5c.GI Fix5c.YG Fix5c.Y Fix5c.YI
      Fix5c.YP Fix5c.R = true := f5c_head
  exact class_count (P := Fix5c.P) (S := Fix5c.S) cw0_letters
    yw7_letters (by decide) hh f5c_yinv f5c_pt0
    (repFSl_all (len := 100) (ns := 8) (by norm_num) fun s hs => by
      have h := f5c_rep_all s hs
      unfold f5cRep at h
      exact h)
    (sortFSl_all (len := 2200) (ns := 3) (by norm_num) fun s hs => by
      have h := f5c_srt_all s hs
      unfold f5cSort at h
      exact h)

theorem cent5c_facts (hP : Nat.card ↥P1408 = 177408000) : CentFacts fix5C :=
  cent_exact hP (elemW_mem _) (Tr2.le_cent fct5c_ok) (Tr2.card_ge fct5c_ok) rec5c.1 rec5c.2.1
    (by decide) (by norm_num)

theorem rec7 : RecFacts fix7.rep fix7.fix 125 288 36000 Fix7.Y Fix7.YI Fix7.R := by
  have hh : headF cw7 sylow5Words fix7.rep fix7.fix 125 Fix7.G Fix7.GI Fix7.YG Fix7.Y Fix7.YI
      Fix7.YP Fix7.R = true := f7_head
  exact class_count (P := Fix7.P) (S := Fix7.S) cw7_letters
    syl5_letters (by decide) hh f7_yinv f7_pt0
    (repFSl_all (len := 100) (ns := 3) (by norm_num) fun s hs => by
      have h := f7_rep_all s hs
      unfold f7Rep at h
      exact h)
    (sortFSl_all (len := 2200) (ns := 17) (by norm_num) fun s hs => by
      have h := f7_srt_all s hs
      unfold f7Sort at h
      exact h)

theorem cent7_facts (hP : Nat.card ↥P1408 = 177408000) : CentFacts fix7 :=
  cent_exact hP (elemW_mem _) (Tr2.le_cent fct7_ok) (Tr2.card_ge fct7_ok) rec7.1 rec7.2.1
    (by decide) (by norm_num)

theorem elemW_conjW {c : List Nat} :
    elemW (h5aWord ++ c ++ h5aWord.reverse) = elemW h5aWord * elemW c * (elemW h5aWord)⁻¹ := by
  rw [elemW_append, elemW_append, elemW_reverse _ (by decide)]

theorem cent5a_le : genC fix5A.cent ≤
    P1408 ⊓ centralizer ({elemW fix5A.rep} : Set (Equiv.Perm (Fin 1408))) := by
  refine (closure_le _).2 ?_
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨elemW_mem c, ?_⟩
  change elemW c ∈ centralizer ({elemW fix5A.rep} : Set (Equiv.Perm (Fin 1408)))
  have hc' : h5aWord ++ c ++ h5aWord.reverse ∈ cent5aW := List.mem_map.2 ⟨c, hc, rfl⟩
  have hm := (Tr2.le_cent fct5a_ok) (subset_closure ⟨_, hc', rfl⟩)
  have hm2 := (Subgroup.mem_inf.1 hm).2
  rw [Subgroup.mem_centralizer_iff] at hm2 ⊢
  rintro _ rfl
  have e := hm2 _ rfl
  unfold rep5aW at e
  rw [elemW_conjW, elemW_conjW] at e
  set h := elemW h5aWord
  calc elemW fix5A.rep * elemW c
      = h⁻¹ * ((h * elemW fix5A.rep * h⁻¹) * (h * elemW c * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * elemW c * h⁻¹) * (h * elemW fix5A.rep * h⁻¹)) * h := by rw [e]
    _ = elemW c * elemW fix5A.rep := by group

theorem cent5a_ge : 2000 ≤ Nat.card (genC fix5A.cent) := by
  have h1 := Tr2.card_ge fct5a_ok
  have hle : genC cent5aW ≤ (genC fix5A.cent).map (MulAut.conj (elemW h5aWord)).toMonoidHom := by
    refine (closure_le _).2 ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hw
    refine ⟨elemW c, subset_closure ⟨c, hc, rfl⟩, ?_⟩
    rw [elemW_conjW]
    rfl
  have h2 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective (MulAut.conj (elemW h5aWord)).injective] at h2
  omega

theorem rec5a : RecFacts fix5A.rep fix5A.fix 3 168 504 Fix5a.Y Fix5a.YI Fix5a.R := by
  have hh : headF cw0 yw3 fix5A.rep fix5A.fix 3 Fix5a.G Fix5a.GI Fix5a.YG Fix5a.Y Fix5a.YI
      Fix5a.YP Fix5a.R = true := f5a_head
  exact class_count (P := Fix5a.P) (S := Fix5a.S) cw0_letters
    yw3_letters (by decide) hh f5a_yinv f5a_pt0
    (repFSl_all (len := 100) (ns := 2) (by norm_num) fun s hs => by
      have h := f5a_rep_all s hs
      unfold f5aRep at h
      exact h)
    (sortFSl_all (len := 2200) (ns := 1) (by norm_num) fun s hs => by
      have h := f5a_srt_all s hs
      unfold f5aSort at h
      exact h)

theorem cent5a_facts (hP : Nat.card ↥P1408 = 177408000) : CentFacts fix5A :=
  cent_exact hP (elemW_mem _) cent5a_le cent5a_ge rec5a.1 rec5a.2.1 (by decide) (by norm_num)

end CFSG.KD.HN1408.FixR

end
