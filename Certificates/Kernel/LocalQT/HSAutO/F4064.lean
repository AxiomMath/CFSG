module

public import Certificates.Kernel.LocalQT.HSAutO.R4064
public import Certificates.Kernel.LocalQT.HSAutO.C4064E0
public import Certificates.Kernel.LocalQT.HSAutO.C4064E1
public import Certificates.Kernel.LocalQT.HSAutO.C4064E2
public import Certificates.Kernel.LocalQT.HSAutO.C4064E3
public import Certificates.Kernel.LocalQT.HSAutO.C4064E4
public import Certificates.Kernel.LocalQT.SV.C4126TB
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.LocalQTRestrSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuterCheckInputs
public import CFSG.Sporadic.SmallOddCore.CentSpec
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SmallOddCore.HSAut

public section

set_option maxRecDepth 400000

#kqb_all CFSG.KD.LQT.HO.A CFSG.KD.LQT.HO.ckO 315

namespace CFSG.KD.LQT.HO

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KS.HSAutO
open CFSG.KD.LQT.C4126 CFSG.QuasithinUnique.Id2519.HSAut CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four CFSG.KC.Restr CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def qPerm (l : ℕ) : Equiv.Perm (Fin 3850) := tp 3850 (qGenT l)

@[expose] noncomputable def qWordPerm (ls : List ℕ) : Equiv.Perm (Fin 3850) := (ls.map qPerm).prod

@[expose] noncomputable def e1 : Equiv.Perm (Fin 3850) := qWordPerm e1Letters

@[expose] noncomputable def e2 : Equiv.Perm (Fin 3850) := qWordPerm e2Letters

@[expose] noncomputable def outerE : Subgroup (Equiv.Perm (Fin 3850)) :=
  Subgroup.closure ({e1, e2} : Set (Equiv.Perm (Fin 3850)))

theorem tabRep_natArr {T : CFSG.Sporadic.Th.Native.Table} (hsz : T.size = 3850)
    (hp : CFSG.Sporadic.SmallOddCore.permOK 3850 T = true) :
    TabRep (natArr T) (tp 3850 T) :=
  ⟨by simp [natArr, hsz], fun i =>
    (co2Rep_natArr_iff (n := 3850)).2 (rep_tp hp) i⟩

theorem e1Letters_lt : ∀ l ∈ e1Letters, l < 4 := by decide

theorem e2Letters_lt : ∀ l ∈ e2Letters, l < 4 := by decide

theorem tabRep_qWordTab' (hq : ∀ l < 4, TabRep (natArr (qGenT l)) (qPerm l)) :
    ∀ {ls : List ℕ}, (∀ l ∈ ls, l < 4) → TabRep (qWordTab ls) (qWordPerm ls)
  | [], _ => by
    simpa [qWordTab, qWordPerm] using
      (TabRep.idTab : TabRep (idTab 3850) (1 : Equiv.Perm (Fin 3850)))
  | l :: ls, h => by
    have h1 := hq l (h l List.mem_cons_self)
    have h2 := tabRep_qWordTab' hq (fun l' hl' => h l' (List.mem_cons_of_mem l hl'))
    simpa [qWordTab, qWordPerm] using h1.comp h2

theorem unpack_getD {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [getElem!_pos _ i (by simp [unpack, hi])]
  simp [unpack]

theorem unpack_sz (n w P : Nat) : (unpack n w P).size = n := by simp [unpack]

theorem idTab_unp {n w : Nat} (hn : szOK n w = true) : idTab n = unpack n w (pidn n w) := by
  obtain ⟨h1, h2⟩ := CFSG.KS.Raw.Orb.szOK_facts hn
  apply Array.ext
  · simp [idTab, unpack]
  · intro i hi _
    have hi' : i < n := by simpa [idTab] using hi
    rw [← getElem!_pos _ i hi, ← getElem!_pos (unpack n w (pidn n w)) i (by simpa [unpack] using hi'),
      unpack_getD hi', CFSG.KS.PF.pg_pidn h1 h2 hi', getElem!_pos _ i hi]
    simp [idTab]

theorem comp_unp {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    comp n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

theorem comp_inv_idT {n : Nat} {t r : Array Nat} (h : CFSG.Monster.B.Co2.Native.isInvA n t r = true) :
    comp n r t = idTab n := by
  apply Array.ext (by simp [comp, idTab])
  intro i h1 _
  have hi : i < n := by simpa [comp] using h1
  simp only [comp, idTab, Array.getElem_ofFn]
  exact (CFSG.Monster.B.Co2.isInvA_spec h hi).2

theorem canon_lt {n w p i : Nat} (hp : canonK n w (mask w) (n * w) p = true) (hi : i < n) :
    pg w (mask w) p i < n := by
  unfold canonK at hp
  obtain ⟨-, hp⟩ := (bAnd_iff _ _).1 hp
  obtain ⟨-, hp⟩ := (bAnd_iff _ _).1 hp
  have := allN_spec hp i hi
  simpa [Nat.blt_eq] using this

theorem beq_eq {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem blt_lt {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa [Nat.blt_eq] using h

theorem sz6 : szOK 35 6 = true := by decide

theorem head_parts : penumHdK (pidn 35 6) A.cnt 20160 A.T A.PL = true ∧ A.cnt = 20160 ∧
    A.k = 2 ∧ repK LAB REP A.cnt = true ∧ r32 LAB 0 = 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := by simpa only [bAnd_iff] using head_ok
  exact ⟨h1, beq_eq h2, beq_eq h3, h4, beq_eq h5⟩

theorem cnt_eq : A.cnt = 20160 := head_parts.2.1

theorem pt_ok {i : Nat} (hi : i < A.cnt) :
    oPtK A.G A.GI A.T A.PL A.POS A.SRT A.SRI LAB WIT CP REP A.cnt i = true := by
  have hi' : i / 64 < 315 := by rw [cnt_eq] at hi; omega
  have hs := A.all (i / 64) hi'
  unfold ckO oSlK at hs
  have h1 := ((bAnd_iff _ _).1 hs).1
  have := allN_spec h1 (i % 64) (Nat.mod_lt _ (by norm_num))
  rw [CFSG.KS.Raw.Orb.strictB_eq] at this
  have e : Nat.add (Nat.mul (i / 64) 64) (i % 64) = i := Nat.div_add_mod' i 64
  rwa [e] at this

theorem vc_ok {s : Nat} (hs : s < 315) {l : Nat} (hl : l < 14) :
    cntL LAB l (Nat.mul s 64) 64 = r32 VC (Nat.add (Nat.mul s 14) l) := by
  have h := A.all s hs
  unfold ckO oSlK at h
  exact beq_eq (allN_spec ((bAnd_iff _ _).1 h).2 l hl)

theorem pen_ok {i : Nat} (hi : i < A.cnt) :
    penumPtK 35 6 (mask 6) (35 * 6) false A.G A.GI 2 A.cnt A.T A.PL A.POS A.SRT A.SRI i = true :=
  ((bAnd_iff _ _).1 (pt_ok hi)).1

theorem cl_ok {i : Nat} (hi : i < A.cnt) : clPtK A.G A.GI A.T LAB WIT CP REP A.cnt i = true :=
  ((bAnd_iff _ _).1 (pt_ok hi)).2

theorem canonT {i : Nat} (hi : i < A.cnt) : canonK 35 6 (mask 6) (35 * 6) (A.T i) = true := by
  have h := pen_ok hi
  unfold penumPtK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  exact ((bAnd_iff _ _).1 h).1

theorem gens_parts {j : Nat} (hj : j < 2) : canonK 35 6 (mask 6) (35 * 6) (A.G j) = true ∧
    canonK 35 6 (mask 6) (35 * 6) (A.GI j) = true ∧
    invEqK 35 6 (mask 6) (35 * 6) (A.G j) (A.GI j) = true := by
  have h := allN_spec gens_ok j hj
  simpa only [bAnd_iff] using h

@[expose] noncomputable def gensO : Array Tab := #[unpack 35 6 (A.G 0), unpack 35 6 (A.G 1)]

@[expose] noncomputable def ginvO : Array Tab := #[unpack 35 6 (A.GI 0), unpack 35 6 (A.GI 1)]

theorem gensO_get {j : Nat} (hj : j < 2) : gensO[j]! = unpack 35 6 (A.G j) := by
  interval_cases j <;> rfl

theorem ginvO_get {j : Nat} (hj : j < 2) : ginvO[j]! = unpack 35 6 (A.GI j) := by
  interval_cases j <;> rfl

theorem gensO_size : gensO.size = 2 := rfl

theorem gensOK : GensOK 35 6 2 A.G gensO :=
  ⟨rfl, fun _ hj => ⟨gensO_get hj, (gens_parts hj).1⟩⟩

@[expose] noncomputable def R : Enum := penumRec 35 6 A.cnt A.T A.PL

theorem R_size : R.tabs.size = A.cnt := by simp [R, penumRec]

theorem R_get {i : Nat} (hi : i < A.cnt) : R.tabs[i]! = unpack 35 6 (A.T i) := by
  rw [getElem!_pos _ i (by rw [R_size]; exact hi)]
  simp [R, penumRec]

theorem enum_ok : enumOK 35 gensO R = true :=
  (penumK_left_sound (cap := 20160) sz6 gensOK head_parts.1 fun _ hi => pen_ok hi).2

abbrev Cn (p : Nat) : Prop := canonK 3850 12 (mask 12) (3850 * 12) p = true

theorem cIdn : Cn idn := by quickRfl

theorem lq_parts {l : Nat} (hl : l < 4) : natArr (qGenT l) = unpack 3850 12 (lq l) ∧ Cn (lq l) :=
  ⟨hsCentTbl_eq (k := 22 + l) (by omega), allN_spec canon_ok l hl⟩

theorem qGenT_ok {l : Nat} (hl : l < 4) :
    CFSG.Sporadic.SmallOddCore.permOK 3850 (qGenT l) = true ∧ (qGenT l).size = 3850 := by
  obtain ⟨h1, h2⟩ := lq_parts hl
  refine ⟨?_, ?_⟩
  · rw [← CFSG.KS.MulH.tabT_natArr (qGenT l), h1]
    exact CFSG.KS.MulH.permOK_unpack h2 (allN_spec hc_perms (22 + l) (by omega))
  · have := congrArg Array.size h1
    simpa [natArr, unpack_sz] using this

theorem tabRep_q {l : Nat} (hl : l < 4) : TabRep (natArr (qGenT l)) (qPerm l) :=
  tabRep_natArr (qGenT_ok hl).2 (qGenT_ok hl).1

theorem wfoldR_cons' (L : Nat → Nat) (l : Nat) (ls : List Nat) :
    wfoldR L (l :: ls) = pc (L l) (wfoldR L ls) :=
  CFSG.KS.Raw.Orb.strictN_eq _ _

theorem foldr_unp {L : Nat → Nat} {F : Nat → Array Nat} : ∀ (ls : List Nat),
    (∀ l ∈ ls, F l = unpack 3850 12 (L l) ∧ Cn (L l)) →
    (ls.map F).foldr (comp 3850) (idTab 3850) = unpack 3850 12 (wfoldR L ls) ∧ Cn (wfoldR L ls)
  | [], _ => ⟨idTab_unp (by decide), cIdn⟩
  | l :: ls, h => by
    obtain ⟨ih1, ih2⟩ := foldr_unp ls fun l' hl' => h l' (List.mem_cons_of_mem l hl')
    obtain ⟨h1, h2⟩ := h l List.mem_cons_self
    rw [List.map_cons, List.foldr_cons, ih1, h1, wfoldR_cons', comp_unp h2 ih2]
    exact ⟨rfl, CFSG.KC.BfsPin.canonK_pcomp h2 ih2⟩

theorem wordE {ls : List Nat} (hls : ∀ l ∈ ls, l < 4) :
    qWordTab ls = unpack 3850 12 (wfoldR lq ls) ∧ Cn (wfoldR lq ls) :=
  foldr_unp ls fun l hl => lq_parts (hls l hl)

theorem word_apply {ls : List Nat} (hls : ∀ l ∈ ls, l < 4) (x : Fin 3850) :
    ((qWordPerm ls x : Fin 3850) : Nat) = img (wfoldR lq ls) x := by
  have hr := tabRep_qWordTab' (fun l hl => tabRep_q hl) hls
  rw [← hr.apply x, (wordE hls).1, unpack_getD x.2]
  rfl

theorem e1_apply (x : Fin 3850) : ((e1 x : Fin 3850) : Nat) = img (wfoldR lq e1Letters) x :=
  word_apply e1Letters_lt x

theorem e2_apply (x : Fin 3850) : ((e2 x : Fin 3850) : Nat) = img (wfoldR lq e2Letters) x :=
  word_apply e2Letters_lt x

theorem q1_apply (x : Fin 3850) : ((qPerm 1 x : Fin 3850) : Nat) = img (lq 1) x := by
  rw [← (tabRep_q (l := 1) (by norm_num)).apply x, (lq_parts (l := 1) (by norm_num)).1,
    unpack_getD x.2]
  rfl

theorem restr_parts : restrK (wfoldR lq e1Letters) (A.G 0) OP = true ∧
    restrK (wfoldR lq e2Letters) (A.G 1) OP = true ∧ qInvK (wfoldR lq e1Letters) (QM 0) = true ∧
    qInvK (wfoldR lq e2Letters) (QM 0) = true ∧ bitK (QM 0) 18 = true ∧
    bitK (QM 0) (img (lq 1) 18) = false := by
  have h := restr_ok
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := by simpa only [bAnd_iff] using h
  exact ⟨h1, h2, h3, h4, h5, by simpa using h6⟩

theorem restrK_parts {E G : Nat} (h : restrK E G OP = true) :
    (∀ i < 35, img E (r32 OP i) = r32 OP (pg 6 (mask 6) G i)) ∧
      (∀ i < 34, r32 OP i < r32 OP (i + 1)) ∧ r32 OP 34 < 3850 := by
  unfold restrK at h
  obtain ⟨h1, h2, h3⟩ := by simpa only [bAnd_iff] using h
  exact ⟨fun i hi => beq_eq (allN_spec h1 i hi), fun i hi => blt_lt (allN_spec h2 i hi),
    blt_lt h3⟩

theorem op_mono : ∀ {i d : Nat}, i + d + 1 < 35 → r32 OP i < r32 OP (i + d + 1)
  | i, 0, h => (restrK_parts restr_parts.1).2.1 i (by omega)
  | i, d + 1, h => by
    have h1 := op_mono (i := i) (d := d) (by omega)
    have h2 := (restrK_parts restr_parts.1).2.1 (i + d + 1) (by omega)
    rw [show i + (d + 1) + 1 = i + d + 1 + 1 by omega]
    omega

theorem op_lt {i : Nat} (hi : i < 35) : r32 OP i < 3850 := by
  have h34 := (restrK_parts restr_parts.1).2.2
  rcases Nat.lt_or_ge i 34 with h | h
  · have := op_mono (i := i) (d := 33 - i) (by omega)
    rw [show i + (33 - i) + 1 = 34 by omega] at this
    omega
  · rw [show i = 34 by omega]
    exact h34

@[expose] noncomputable def fO (i : Fin 35) : Fin 3850 := ⟨r32 OP i, op_lt i.2⟩

theorem fO_inj : Function.Injective fO := by
  intro i j h
  have h' : r32 OP i = r32 OP j := congrArg Fin.val h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · have := op_mono (i := i) (d := j - i - 1) (by omega)
    rw [show (i : Nat) + (j - i - 1) + 1 = j by omega] at this
    omega
  · have := op_mono (i := j) (d := i - j - 1) (by omega)
    rw [show (j : Nat) + (i - j - 1) + 1 = i by omega] at this
    omega

@[expose] def Oset : Set (Fin 3850) := Set.range fO

theorem sig_lt {j : Nat} (hj : j < 2) (i : Fin 35) : pg 6 (mask 6) (A.G j) i < 35 :=
  canon_lt (gens_parts hj).1 i.2

theorem e1_f (i : Fin 35) :
    e1 (fO i) = fO ⟨pg 6 (mask 6) (A.G 0) i, sig_lt (by norm_num) i⟩ := by
  apply Fin.ext
  rw [e1_apply]
  exact (restrK_parts restr_parts.1).1 i i.2

theorem e2_f (i : Fin 35) :
    e2 (fO i) = fO ⟨pg 6 (mask 6) (A.G 1) i, sig_lt (by norm_num) i⟩ := by
  apply Fin.ext
  rw [e2_apply]
  exact (restrK_parts restr_parts.2.1).1 i i.2

theorem e1_mem : e1 ∈ stabP Oset :=
  mem_stabP_of_mapsTo (by rintro _ ⟨i, rfl⟩; exact ⟨_, (e1_f i).symm⟩)

theorem e2_mem : e2 ∈ stabP Oset :=
  mem_stabP_of_mapsTo (by rintro _ ⟨i, rfl⟩; exact ⟨_, (e2_f i).symm⟩)

theorem le_stab : outerE ≤ stabP Oset := by
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  rcases hg with rfl | rfl
  · exact e1_mem
  · exact e2_mem

@[expose] noncomputable def eqv : Fin 35 ≃ Oset := Equiv.ofInjective fO fO_inj

@[expose] noncomputable def rho : outerE →* Equiv.Perm (Fin 35) :=
  eqv.symm.permCongrHom.toMonoidHom.comp ((resHom Oset).comp (Subgroup.inclusion le_stab))

theorem rho_apply {g : outerE} {i k : Fin 35}
    (h : (g : Equiv.Perm (Fin 3850)) (fO i) = fO k) : rho g i = k := by
  have e : resHom Oset (Subgroup.inclusion le_stab g) (eqv i) = eqv k := by
    apply Subtype.ext
    rw [resHom_apply]
    exact h
  simp only [rho, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe,
    Equiv.permCongr_apply, Equiv.symm_symm]
  rw [e, Equiv.symm_apply_apply]

theorem e1_memE : e1 ∈ outerE := Subgroup.subset_closure (by simp)

theorem e2_memE : e2 ∈ outerE := Subgroup.subset_closure (by simp)

@[expose] noncomputable def Aset : Set (Equiv.Perm (Fin 35)) :=
  {rho ⟨e1, e1_memE⟩, rho ⟨e2, e2_memE⟩}

theorem tabRep_r1 : TabRep gensO[0]! (rho ⟨e1, e1_memE⟩) := by
  refine ⟨by rw [gensO_get (by norm_num), unpack_sz], fun i => ?_⟩
  rw [gensO_get (by norm_num), unpack_getD i.2, rho_apply (e1_f i)]

theorem tabRep_r2 : TabRep gensO[1]! (rho ⟨e2, e2_memE⟩) := by
  refine ⟨by rw [gensO_get (by norm_num), unpack_sz], fun i => ?_⟩
  rw [gensO_get (by norm_num), unpack_getD i.2, rho_apply (e2_f i)]

theorem hA : ∀ a ∈ Aset, ∃ j < gensO.size, TabRep gensO[j]! a := by
  intro a ha
  rcases ha with rfl | rfl
  · exact ⟨0, by rw [gensO_size]; norm_num, tabRep_r1⟩
  · exact ⟨1, by rw [gensO_size]; norm_num, tabRep_r2⟩

theorem hgens : ∀ j < gensO.size, ∃ a ∈ Aset, TabRep gensO[j]! a := by
  intro j hj
  rw [gensO_size] at hj
  interval_cases j
  · exact ⟨_, Or.inl rfl, tabRep_r1⟩
  · exact ⟨_, Or.inr rfl, tabRep_r2⟩

theorem enumA : Enumerates (Subgroup.closure Aset) R.tabs.toList :=
  enumerates_closure hA hgens enum_ok

theorem card_A : Nat.card (Subgroup.closure Aset) = 20160 := by
  rw [enumA.card, Array.length_toList, R_size, cnt_eq]

theorem rho_range : rho.range = Subgroup.closure Aset := by
  have htop : (⊤ : Subgroup outerE) =
      Subgroup.closure ((Subtype.val : outerE → Equiv.Perm (Fin 3850)) ⁻¹' {e1, e2}) :=
    (Subgroup.closure_closure_coe_preimage).symm
  rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Aset]
  constructor
  · rintro ⟨g, hg | hg, rfl⟩
    · left
      congr 1
      exact Subtype.ext hg
    · right
      congr 1
      exact Subtype.ext hg
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩

@[expose] noncomputable def CD : ClassData :=
  ⟨Array.ofFn (n := A.cnt) fun k => r32 LAB k.val, Array.ofFn (n := 14) fun l => r32 REP l.val,
    Array.ofFn (n := A.cnt) fun k => r32 WIT k.val⟩

theorem CD_lab {k : Nat} (hk : k < A.cnt) : CD.lab[k]! = r32 LAB k := by
  rw [getElem!_pos _ k (by simpa [CD] using hk)]
  simp [CD]

theorem CD_wit {k : Nat} (hk : k < A.cnt) : CD.wit[k]! = r32 WIT k := by
  rw [getElem!_pos _ k (by simpa [CD] using hk)]
  simp [CD]

theorem CD_rep {l : Nat} (hl : l < 14) : CD.reps[l]! = r32 REP l := by
  rw [getElem!_pos _ l (by simpa [CD] using hl)]
  simp [CD]

theorem cl_parts {k : Nat} (hk : k < A.cnt) : r32 LAB k < 14 ∧ r32 WIT k < A.cnt ∧
    po (A.T (r32 WIT k)) (A.T (r32 REP (r32 LAB k))) = po (A.T k) (A.T (r32 WIT k)) ∧
    ∀ j < 2, r32 CP (Nat.add (Nat.mul k 2) j) < A.cnt ∧
      A.T (r32 CP (Nat.add (Nat.mul k 2) j)) = po (po (A.G j) (A.T k)) (A.GI j) ∧
      r32 LAB (r32 CP (Nat.add (Nat.mul k 2) j)) = r32 LAB k := by
  have h := cl_ok hk
  unfold clPtK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := by simpa only [bAnd_iff] using h
  refine ⟨blt_lt h1, blt_lt h2, beq_eq h3, fun j hj => ?_⟩
  have h5 := allN_spec h4 j hj
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h5
  obtain ⟨a, b, c⟩ := by simpa only [bAnd_iff] using h5
  exact ⟨blt_lt a, beq_eq b, beq_eq c⟩

theorem nodupR : R.tabs.toList.Nodup := enumA.nodup

theorem conj_eq {k j : Nat} (hk : k < A.cnt) (hj : j < 2) :
    conjTab 35 gensO[j]! ginvO[j]! R.tabs[k]! = R.tabs[r32 CP (Nat.add (Nat.mul k 2) j)]! := by
  obtain ⟨hc, ht, -⟩ := (cl_parts hk).2.2.2 j hj
  have g := gens_parts hj
  rw [R_get hc, ht, gensO_get hj, ginvO_get hj, R_get hk]
  unfold conjTab
  rw [comp_unp g.1 (canonT hk), comp_unp (CFSG.KC.BfsPin.canonK_pcomp g.1 (canonT hk)) g.2.1]
  rfl

theorem wit_eq {k : Nat} (hk : k < A.cnt) :
    comp 35 R.tabs[r32 WIT k]! R.tabs[r32 REP (r32 LAB k)]! =
      comp 35 R.tabs[k]! R.tabs[r32 WIT k]! := by
  obtain ⟨hl, hw, he, -⟩ := cl_parts hk
  have hr := allN_spec head_parts.2.2.2.1 (r32 LAB k) hl
  rw [CFSG.KS.Raw.Orb.strictB_eq] at hr
  have hr' := blt_lt ((bAnd_iff _ _).1 hr).1
  rw [R_get hw, R_get hr', R_get hk, comp_unp (canonT hw) (canonT hr'),
    comp_unp (canonT hk) (canonT hw)]
  exact congrArg (unpack 35 6) he

theorem rep_parts {l : Nat} (hl : l < 14) : r32 REP l < A.cnt ∧ r32 LAB (r32 REP l) = l := by
  have hr := allN_spec head_parts.2.2.2.1 l hl
  rw [CFSG.KS.Raw.Orb.strictB_eq] at hr
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 hr
  exact ⟨blt_lt a, beq_eq b⟩

theorem cntL_eq (l lo : Nat) : ∀ len : Nat,
    cntL LAB l lo len = ((List.range len).filter fun d => r32 LAB (lo + d) == l).length
  | 0 => rfl
  | len + 1 => by
    have ih := cntL_eq l lo len
    have e : cntL LAB l lo (len + 1) = strictN (cntL LAB l lo len) (fun a =>
        nIf(Nat.beq (r32 LAB (Nat.add lo len)) l, Nat.succ a, a)) := rfl
    rw [e, CFSG.KS.Raw.Orb.strictN_eq, CFSG.KS.Raw.Orb.nIf_eq, List.range_succ,
      List.filter_append, List.length_append, ← ih]
    have hbe : (r32 LAB (lo + len) == l) = Nat.beq (r32 LAB (Nat.add lo len)) l := rfl
    cases hb : Nat.beq (r32 LAB (Nat.add lo len)) l
    · simp only [hbe, hb, Bool.false_eq_true, ↓reduceIte, List.filter_cons, List.filter_nil,
        List.length_nil, Nat.add_zero]
    · simp only [hbe, hb, ↓reduceIte, List.filter_cons, List.filter_nil, List.length_cons,
        List.length_nil]

theorem sumVC_succ (l c : Nat) :
    sumVC VC l (c + 1) = sumVC VC l c + r32 VC (Nat.add (Nat.mul c 14) l) := by
  have e : sumVC VC l (c + 1) = strictN (sumVC VC l c) (fun a =>
      Nat.add a (r32 VC (Nat.add (Nat.mul c (nat_lit 14)) l))) := rfl
  rw [e, CFSG.KS.Raw.Orb.strictN_eq]
  rfl

theorem count_chunks {l : Nat} (hl : l < 14) : ∀ c ≤ 315,
    ((List.range (64 * c)).filter fun k => r32 LAB k == l).length = sumVC VC l c
  | 0, _ => rfl
  | c + 1, hc => by
    rw [show 64 * (c + 1) = 64 * c + 64 by ring, List.range_add, List.filter_append,
      List.length_append, count_chunks hl c (by omega), sumVC_succ, ← vc_ok (by omega) hl,
      cntL_eq, List.filter_map, List.length_map]
    congr 2
    apply List.filter_congr
    intro d _
    simp only [Function.comp_apply]
    rw [show Nat.mul c 64 = 64 * c from Nat.mul_comm c 64]

theorem counts {l : Nat} (hl : l < 14) :
    countBelow R.tabs.size (fun k => CD.lab[k]! == l) = classSizes[l]! := by
  have hs : sumVC VC l 315 = classSizes[l]! :=
    beq_eq (a := sumVC VC l 315) (b := classSizes[l]!) (allN_spec sum_ok l hl)
  rw [← hs, ← count_chunks hl 315 le_rfl, countBelow, R_size, cnt_eq,
    show (64 * 315 : Nat) = 20160 from rfl]
  have e : (List.range 20160).filter (fun k => CD.lab[k]! == l) =
      (List.range 20160).filter (fun k => r32 LAB k == l) := by
    apply List.filter_congr
    intro k hk
    rw [List.mem_range] at hk
    rw [CD_lab (by rw [cnt_eq]; exact hk)]
  rw [e]

theorem invsO : invsOK 35 gensO ginvO = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq, allBelow_eq_true]
  refine ⟨rfl, fun k hk => ?_⟩
  have hk' : k < 2 := by simpa [gensO_size] using hk
  rw [ginvO_get hk', gensO_get hk']
  have g := gens_parts hk'
  exact ⟨unpack_sz _ _ _, comp_inv_idT (invEqK_sound g.2.2).2⟩

theorem T0 : R.tabs[0]! = idTab 35 := by
  have hh := head_parts.1
  unfold penumHdK at hh
  obtain ⟨-, -, h3, -⟩ := by simpa only [bAnd_iff] using hh
  rw [R_get (by rw [cnt_eq]; norm_num), beq_eq h3, idTab_unp sz6]

theorem cls_ok : classOKGen 35 R.tabs gensO ginvO CD classSizes = true := by
  have hsz : classSizes.size = 14 := rfl
  simp only [classOKGen, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allBelow_eq_true,
    and_assoc]
  refine ⟨invsO, fun k hk => posOf_eq nodupR hk, fun k hk j hj => ?_, by simp [CD, hsz],
    fun l hl => ?_, fun k hk => ?_, fun l hl => counts (by omega),
    (by rw [R_size, cnt_eq]; norm_num), T0, ?_⟩
  · have hk' : k < A.cnt := by rwa [R_size] at hk
    have hj' : j < 2 := by simpa [gensO_size] using hj
    obtain ⟨hc, -, hlab⟩ := (cl_parts hk').2.2.2 j hj'
    rw [conj_eq hk' hj', posOf_eq nodupR (by rw [R_size]; exact hc)]
    refine ⟨(CFSG.KS.PEnum.found_indexOf_iff _ _).2 ⟨_, by rw [R_size]; exact hc, rfl⟩, ?_⟩
    rw [CD_lab hc, CD_lab hk', hlab]
  · rw [hsz] at hl
    obtain ⟨h1, h2⟩ := rep_parts hl
    rw [CD_rep hl, CD_lab h1, h2]
    exact ⟨by rw [R_size]; exact h1, rfl⟩
  · have hk' : k < A.cnt := by rwa [R_size] at hk
    obtain ⟨hl, hw, -⟩ := cl_parts hk'
    rw [CD_lab hk', CD_wit hk', CD_rep hl, hsz, R_size]
    exact ⟨hl, hw, wit_eq hk'⟩
  · rw [CD_lab (by rw [cnt_eq]; norm_num)]
    exact head_parts.2.2.2.2

theorem qPerm_one_not_mem : qPerm 1 ∉ outerE := by
  let Q : Set (Fin 3850) := {x | bitK (QM 0) x = true}
  have hQ1 : ∀ x ∈ Q, e1 x ∈ Q := by
    intro x hx
    have := allN_spec restr_parts.2.2.1 x x.2
    have hx' : bitK (QM 0) (x : Nat) = true := hx
    rw [CFSG.KS.Raw.Orb.bIf_eq] at this
    simp only [hx', ↓reduceIte] at this
    show bitK (QM 0) (e1 x) = true
    rw [e1_apply]
    exact this
  have hQ2 : ∀ x ∈ Q, e2 x ∈ Q := by
    intro x hx
    have := allN_spec restr_parts.2.2.2.1 x x.2
    have hx' : bitK (QM 0) (x : Nat) = true := hx
    rw [CFSG.KS.Raw.Orb.bIf_eq] at this
    simp only [hx', ↓reduceIte] at this
    show bitK (QM 0) (e2 x) = true
    rw [e2_apply]
    exact this
  have hle : outerE ≤ stabP Q := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    rcases hg with rfl | rfl
    · exact mem_stabP_of_mapsTo hQ1
    · exact mem_stabP_of_mapsTo hQ2
  intro hq
  have h18 : (⟨18, by norm_num⟩ : Fin 3850) ∈ Q := restr_parts.2.2.2.2.1
  have := (mem_stabP.1 (hle hq) ⟨18, by norm_num⟩).2 h18
  have e : bitK (QM 0) (qPerm 1 ⟨18, by norm_num⟩) = true := this
  rw [q1_apply] at e
  rw [restr_parts.2.2.2.2.2] at e
  exact Bool.false_ne_true e

theorem outer_facts :
    (allBelow 4 fun l => CFSG.Sporadic.SmallOddCore.permOK 3850 (qGenT l) &&
      (qGenT l).size == 3850) = true ∧
    qPerm 1 ∉ outerE ∧
    ∃ ρ : outerE →* Equiv.Perm (Fin 35), Nat.card ρ.range = 20160 ∧
      ∃ e : Fin classSizes.size ≃ ConjClasses ρ.range,
        (∀ l, Nat.card (e l).carrier = classSizes[l.val]!) ∧
        ∃ l₀ : Fin classSizes.size, l₀.val = 0 ∧ e l₀ = ConjClasses.mk 1 := by
  refine ⟨?_, qPerm_one_not_mem, rho, ?_⟩
  · rw [allBelow_eq_true]
    intro l hl
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact qGenT_ok hl
  · rw [rho_range]
    exact ⟨card_A, classes_of_classOKGen hA enumA cls_ok⟩

end CFSG.KD.LQT.HO

end
