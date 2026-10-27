module

public import Certificates.Kernel.Sporadic.Fi22.Five8124K
public import Certificates.Kernel.Sporadic.Fi22.F1Outer
public import CFSG.Certificates.Kernel.Fi22Five8124Sound
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.RankThree.Native.Fi22FiveDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fv8124

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CertificateChecks.KernelSpor
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore CFSG.KC.Fv8124 CFSG.AGLEmbedding.KFactProofs.Fi22Five
open scoped commutatorElement

@[expose] noncomputable def pe (p : ℕ) : Equiv.Perm (Fin 3510) := permOfArr 3510 (unpack 3510 12 p)

theorem hsz : szOK 3510 12 = true := by decide +kernel

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem rep_pe {p : ℕ} (hp : PP 3510 12 p) : Rep 3510 (unpack 3510 12 p) (pe p) :=
  rep_of_validA (CFSG.KC.B3S3K.validA_of (CFSG.KC.Misc.ArrEnum.permB_of_pp hp))

theorem PP_of_isP {p : ℕ} (h : isP p = true) : PP 3510 12 p := by
  unfold isP at h
  rw [Bool.and_eq_true] at h
  exact PP_of_permOK hsz h.2

theorem PP_c {p q : ℕ} (hp : PP 3510 12 p) (hq : PP 3510 12 q) : PP 3510 12 (Fi22X.c p q) :=
  hp.mul hq

theorem PP_inv {p : ℕ} (hp : PP 3510 12 p) : PP 3510 12 (Fi22X.inv p) := hp.inv

theorem PP_id : PP 3510 12 idP := PP.id hsz

theorem pe_c {p q : ℕ} (hp : PP 3510 12 p) (hq : PP 3510 12 q) :
    pe (Fi22X.c p q) = pe p * pe q := by
  have h := rep_compA (rep_pe hp) (rep_pe hq)
  rw [compA_PP hp hq] at h
  exact permOfArr_eq_of_rep h

theorem pe_inv {p : ℕ} (hp : PP 3510 12 p) : pe (Fi22X.inv p) = (pe p)⁻¹ := by
  have h := rep_inv_of_validA (CFSG.KC.B3S3K.validA_of (CFSG.KC.Misc.ArrEnum.permB_of_pp hp))
  rw [invCand_PP hp] at h
  exact permOfArr_eq_of_rep h

theorem pe_id : pe idP = 1 := by
  have h : Rep 3510 (unpack 3510 12 idP) 1 := by
    rw [idP, ← idA_eq hsz]
    exact rep_idA
  exact permOfArr_eq_of_rep h

theorem pe_eq_iff {p q : ℕ} (hp : PP 3510 12 p) (hq : PP 3510 12 q) :
    pe p = pe q ↔ Nat.beq p q = true := by
  rw [← eqA_iff (rep_pe hp) (rep_pe hq), eqA_PP hp hq]

theorem PP_pw {p : ℕ} (hp : PP 3510 12 p) (k : ℕ) : PP 3510 12 (pwK p k) := by
  induction k with
  | zero => exact PP_id
  | succ k ih => exact PP_c hp ih

theorem pe_pw {p : ℕ} (hp : PP 3510 12 p) (k : ℕ) : pe (pwK p k) = pe p ^ k := by
  induction k with
  | zero => exact pe_id
  | succ k ih =>
    change pe (Fi22X.c p (pwK p k)) = _
    rw [pe_c hp (PP_pw hp k), ih, pow_succ']

theorem pe_apply {p : ℕ} (hp : PP 3510 12 p) (x : Fin 3510) : ((pe p x : Fin 3510) : ℕ) = ev p x := by
  rw [← rep_pe hp x, unpack_getElem!, if_pos x.2]
  rfl

theorem mem_P {p : ℕ}
    (hp : PP 3510 12 p) : pe p ∈ fi22P ↔ Fi22X.siftP p = true := by
  rw [← fi22InP_iff (rep_pe hp), Fi22LabA.fi22InP_eq rfl hp.1]

theorem allN_spec' {m : ℕ} {f : ℕ → Bool} (h : allN m f = true) {i : ℕ} (hi : i < m) :
    f i = true :=
  Orb.allN_iff.1 h i hi

theorem memE_spec {x : ℕ} (h : memE x = true) : ∃ i < 60, Fv8124E.T i = x := by
  unfold memE at h
  rw [Bool.not_eq_true'] at h
  by_contra hc
  push Not at hc
  rw [← Bool.not_eq_true, Orb.allN_iff] at h
  exact h fun i hi => by
    rw [Bool.not_eq_true']
    cases e : Nat.beq (Fv8124E.T i) x
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) (hc i hi)

theorem fiveArr_eq {k : ℕ} (hk : k < 8) : fi22FiveArr k = unpack 3510 12 (Fv8124T.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound Fv8124T.all k hk
  rw [← Fv8124T.eq] at h
  exact h

theorem aArr_eq : fi22FiveAArr = unpack 3510 12 A :=
  Fi22F1O.arr3510_eq (by norm_num)

theorem okQ' : isP Q1 = true ∧ isP Q2 = true ∧ Nat.beq (Fi22X.c Q1 Q2) (Fi22X.c Q2 Q1) = true ∧
    Nat.beq (pwK Q1 5) idP = true ∧ Nat.beq (pwK Q2 5) idP = true ∧ Nat.beq Q1 idP = false ∧
    allN 5 (fun e => !(Nat.beq Q2 (pwK Q1 e))) = true := by
  have h := okQ
  simp only [strictB_eq, chkQ, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem okW' : isP W = true ∧ Nat.beq (Fi22X.c W W) idP = true ∧ Nat.beq W idP = false ∧
    Fi22X.siftP W = false ∧ Fi22X.cn (Fi22X.c Fi22X.GO W) = true ∧
    Fi22X.siftP (Fi22X.c Fi22X.GO W) = true := by
  have h := okW
  simp only [strictB_eq, chkW, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem okH' {j : ℕ} (hj : j < 5) : isP (H (j + 1)) = true ∧ Fi22X.siftP (H (j + 1)) = true ∧
    Nat.beq (Fi22X.c (H (j + 1)) (lineK Q1 Q2 (j + 1))) (Fi22X.c Q1 (H (j + 1))) = true ∧
    Nat.beq (Fi22X.c (H (j + 1)) W) (Fi22X.c W (H (j + 1))) = true := by
  have h := okH
  simp only [strictB_eq] at h
  have h' := allN_spec' h hj
  simp only [strictB_eq, chkH, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
  exact ⟨h1, h2, h3, h4⟩

@[expose] noncomputable def D1 : ℕ := Fi22X.c (Fi22X.c A Q2) (Fi22X.c (Fi22X.inv A) (Fi22X.inv Q2))

theorem ok0' : isP A = true ∧ Fi22X.siftP Q1 = true ∧ Fi22X.siftP Q2 = true ∧
    Fi22X.siftP A = true ∧
    Nat.beq (Fi22X.c A Q1) (Fi22X.c Q1 A) = true ∧ Nat.beq (Fi22X.c W Q1) (Fi22X.c Q1 W) = true ∧
    Nat.beq (Fi22X.c A W) (Fi22X.c W A) = true ∧ Nat.beq (Fi22X.c Q2 W) (Fi22X.c W Q2) = true ∧
    Nat.beq (Fi22X.c (Fi22X.c A (Fi22X.c (Fi22X.inv Q2) (Fi22X.inv Q2)))
        (Fi22X.c (Fi22X.inv Q2) (Fi22X.c (Fi22X.inv Q2) (Fi22X.c A (Fi22X.inv Q2)))))
      (Fi22X.c Q2 (Fi22X.c (Fi22X.c (Fi22X.inv Q2) (Fi22X.c (Fi22X.inv Q2)
        (Fi22X.c A (Fi22X.inv Q2)))) (Fi22X.c A (Fi22X.c (Fi22X.inv Q2) (Fi22X.inv Q2))))) =
        true ∧
    Nat.beq Fv8124E.ng 2 = true ∧ Nat.beq Fv8124E.N 60 = true ∧
    Nat.beq (Fv8124E.G 0) D1 = true ∧ Nat.beq (Fv8124E.G 1) Q2 = true ∧
    memE (Fi22X.c A (Fi22X.c D1 (Fi22X.inv A))) = true ∧
    memE (Fi22X.c A (Fi22X.c Q2 (Fi22X.inv A))) = true ∧
    memE (Fi22X.c Q2 (Fi22X.c D1 (Fi22X.inv Q2))) = true ∧
    Nat.beq (Fi22X.c D1 Q2) (Fi22X.c Q2 D1) = false := by
  have h := ok0
  simp only [strictB_eq, chk0, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, -⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩, h18⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11, h12, h13, h14, h15, h16, h17, h18⟩

theorem okD' : (allN 60 fun i => orbRow (fi22FiveOrbits[0]!) (Fv8124E.T i)) = true ∧
    (allN 5 fun e => !(memE (Fi22X.c A (pwK (Fi22X.inv Q1) e)))) = true ∧
    (allN 60 fun i =>
      difAt (fun p => ev A (ev (Fv8124E.T i) (ev (Fv8124E.G 0) p)))
          (fun p => ev (Fv8124E.G 0) (ev A (ev (Fv8124E.T i) p))) ||
        difAt (fun p => ev A (ev (Fv8124E.T i) (ev Q2 p)))
          (fun p => ev Q2 (ev A (ev (Fv8124E.T i) p)))) = true := by
  have h := okD
  simp only [strictB_eq, chkD, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem pQ1 : PP 3510 12 Q1 := PP_of_isP okQ'.1
theorem pQ2 : PP 3510 12 Q2 := PP_of_isP okQ'.2.1
theorem pW : PP 3510 12 W := PP_of_isP okW'.1
theorem pA : PP 3510 12 A := PP_of_isP ok0'.1

theorem comm_of {p q : ℕ} (hp : PP 3510 12 p) (hq : PP 3510 12 q)
    (h : Nat.beq (Fi22X.c p q) (Fi22X.c q p) = true) : pe p * pe q = pe q * pe p := by
  rw [← pe_c hp hq, ← pe_c hq hp]
  exact (pe_eq_iff (PP_c hp hq) (PP_c hq hp)).2 h

theorem ne_of {p q : ℕ} (hp : PP 3510 12 p) (hq : PP 3510 12 q) (h : Nat.beq p q = false) :
    pe p ≠ pe q := fun e => by
  rw [(pe_eq_iff hp hq).1 e] at h
  exact Bool.noConfusion h

theorem pD1 : PP 3510 12 D1 := PP_c (PP_c pA pQ2) (PP_c (PP_inv pA) (PP_inv pQ2))

theorem pe_D1 : pe D1 = ⁅pe A, pe Q2⁆ := by
  rw [D1, pe_c (PP_c pA pQ2) (PP_c (PP_inv pA) (PP_inv pQ2)), pe_c pA pQ2,
    pe_c (PP_inv pA) (PP_inv pQ2), pe_inv pA, pe_inv pQ2, commutatorElement_def]
  group

theorem eG : Fv8124E.G 0 = D1 ∧ Fv8124E.G 1 = Q2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := ok0'
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem eNg : Fv8124E.ng = 2 ∧ Fv8124E.N = 60 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h1, h2, -⟩ := ok0'
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem pG : ∀ k < 2, PP 3510 12 (Fv8124E.G k) := fun k hk => by
  interval_cases k
  · rw [eG.1]
    exact pD1
  · rw [eG.2]
    exact pQ2

@[expose] noncomputable def gsD : Array (Array ℕ) :=
  #[unpack 3510 12 (Fv8124E.G 0), unpack 3510 12 (Fv8124E.G 1)]

theorem bfsD : bfsK 3510 12 2 Fv8124E.G 60 Fv8124E.T Fv8124E.E Fv8124E.S = true := by
  have h := Fv8124E.ok
  rw [eNg.1, eNg.2] at h
  exact h

theorem keysD : keysSK 3510 12 fi22BaseArr.toList 60 Fv8124E.T Fv8124E.SK = true := by
  have h := Fv8124E.keys
  rw [eNg.2] at h
  exact h

theorem base_lt : ∀ p ∈ fi22BaseArr.toList, p < 3510 := by decide

theorem enumD : enumOK 3510 gsD fi22BaseArr.toList (enumBfs 3510 gsD fi22BaseArr.toList 60) = true ∧
    (enumBfs 3510 gsD fi22BaseArr.toList 60).pts.size = 60 ∧
    ∀ i < 60, (enumBfs 3510 gsD fi22BaseArr.toList 60).pts[i]! = unpack 3510 12 (Fv8124E.T i) :=
  CFSG.KC.B3S3K.enum_of (ng := 2) (N := 60) (fuel := 60)
    ⟨rfl, fun j (hj : j < 2) => by interval_cases j <;> rfl⟩
    (fun k hk => CFSG.KC.Misc.ArrEnum.permB_of_pp (pG k hk)) bfsD base_lt keysD le_rfl

theorem pT : ∀ i < 60, PP 3510 12 (Fv8124E.T i) :=
  PP_pts bfsD fun k hk => CFSG.KC.Misc.ArrEnum.permB_of_pp (pG k hk)

abbrev D0 : Subgroup (Equiv.Perm (Fin 3510)) := Subgroup.closure ({⁅pe A, pe Q2⁆, pe Q2} : Set _)

theorem permsA_gsD : permsA 3510 gsD = ({⁅pe A, pe Q2⁆, pe Q2} : Set _) := by
  have e0 : permOfArr 3510 gsD[0]! = ⁅pe A, pe Q2⁆ := by
    change pe (Fv8124E.G 0) = _
    rw [eG.1, pe_D1]
  have e1 : permOfArr 3510 gsD[1]! = pe Q2 := by
    change pe (Fv8124E.G 1) = _
    rw [eG.2]
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := hk
    interval_cases k
    · exact Or.inl e0
    · exact Or.inr e1
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, e0⟩
    · exact ⟨1, by decide, e1⟩

theorem mem_D0 {t : Equiv.Perm (Fin 3510)} : t ∈ D0 ↔ ∃ i < 60, pe (Fv8124E.T i) = t := by
  obtain ⟨hE, hS, hT⟩ := enumD
  have h := ((enumOK_spec base_lt hE).1 t)
  rw [permsA_gsD, hS] at h
  rw [h]
  constructor
  · rintro ⟨i, hi, e⟩
    exact ⟨i, hi, by rw [← e, hT i hi]; rfl⟩
  · rintro ⟨i, hi, e⟩
    exact ⟨i, hi, by rw [hT i hi]; exact e⟩

theorem pe_T_mem {i : ℕ} (hi : i < 60) : pe (Fv8124E.T i) ∈ D0 := mem_D0.2 ⟨i, hi, rfl⟩

theorem card_D0 : Nat.card D0 = 60 := by
  obtain ⟨hE, hS, -⟩ := enumD
  have h := (enumOK_spec base_lt hE).2.1
  rw [permsA_gsD, hS] at h
  exact h

theorem mem_D0_of_memE {y : ℕ} (hy : PP 3510 12 y) (h : memE y = true) : pe y ∈ D0 := by
  obtain ⟨i, hi, rfl⟩ := memE_spec h
  exact pe_T_mem hi

theorem memE_of {i y : ℕ} (hi : i < 60) (h : Fv8124E.T i = y) : memE y = true := by
  unfold memE
  rw [Bool.not_eq_true']
  cases e : allN 60 (fun i => !(Nat.beq (Fv8124E.T i) y))
  · rfl
  · have := allN_spec' e hi
    rw [h, Nat.beq_refl] at this
    exact Bool.noConfusion this

@[expose] def O0 : Finset (Fin 3510) :=
  ((fi22FiveOrbits[0]!).map fun o => (⟨o % 3510, Nat.mod_lt _ (by norm_num)⟩ : Fin 3510)).toFinset

theorem orb0_eq : fi22FiveOrbits[0]! = [19, 30, 561, 2344, 3461] := rfl

theorem O0_lt : ∀ o ∈ fi22FiveOrbits[0]!, o < 3510 := by
  rw [orb0_eq]
  decide

theorem card_O0 : O0.card = 5 := by
  rw [O0, orb0_eq]
  rfl

theorem mem_O0 {p : Fin 3510} : p ∈ O0 ↔ (p : ℕ) ∈ fi22FiveOrbits[0]! := by
  simp only [O0, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨o, ho, rfl⟩
    simpa [Nat.mod_eq_of_lt (O0_lt o ho)] using ho
  · intro hp
    exact ⟨p, hp, Fin.ext (Nat.mod_eq_of_lt p.2)⟩

theorem simple_D0 : IsSimpleGroup D0 := by
  have horb := okD'.1
  apply isSimpleGroup_of_faithful_five O0 card_O0 _ _ card_D0
  · intro g hg p hp
    obtain ⟨i, hi, rfl⟩ := mem_D0.1 hg
    have h := allN_spec' horb hi
    unfold orbRow at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    rw [mem_O0] at hp ⊢
    have hc := h.1 _ hp
    rw [List.contains_iff_mem] at hc
    rwa [pe_apply (pT i hi)]
  · intro g hg hfix
    obtain ⟨i, hi, rfl⟩ := mem_D0.1 hg
    have h := allN_spec' horb hi
    unfold orbRow at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h.2 with h2 | h2
    · exfalso
      rw [Bool.eq_false_iff] at h2
      apply h2
      rw [List.all_eq_true]
      intro o ho
      have hlt := O0_lt o ho
      have hp : (⟨o, hlt⟩ : Fin 3510) ∈ O0 := mem_O0.2 ho
      have := congrArg Fin.val (hfix _ hp)
      rw [pe_apply (pT i hi)] at this
      rw [Nat.beq_eq]
      exact this
    · rw [← pe_id]
      exact (pe_eq_iff (pT i hi) PP_id).2 h2

theorem get_ev {p : ℕ} (hp : PP 3510 12 p) {x : ℕ} (hx : x < 3510) :
    (unpack 3510 12 p)[x]! = ev p x ∧ ev p x < 3510 := by
  have h1 : (unpack 3510 12 p)[x]! = ev p x := by
    rw [unpack_getElem!, if_pos hx]
    rfl
  exact ⟨h1, h1 ▸ (rep_pe hp).lt hx⟩

theorem get3 {p q r : ℕ} (hp : PP 3510 12 p) (hq : PP 3510 12 q) (hr : PP 3510 12 r) {x : ℕ}
    (hx : x < 3510) :
    (compA 3510 (compA 3510 (unpack 3510 12 p) (unpack 3510 12 q)) (unpack 3510 12 r))[x]! =
      ev p (ev q (ev r x)) := by
  obtain ⟨r1, r2⟩ := get_ev hr hx
  obtain ⟨q1, q2⟩ := get_ev hq r2
  rw [compA_get hx, r1, compA_get r2, q1, (get_ev hp q2).1]

theorem get3' {p q r : ℕ} (hp : PP 3510 12 p) (hq : PP 3510 12 q) (hr : PP 3510 12 r) {x : ℕ}
    (hx : x < 3510) :
    (compA 3510 (unpack 3510 12 r) (compA 3510 (unpack 3510 12 p) (unpack 3510 12 q)))[x]! =
      ev r (ev p (ev q x)) := by
  obtain ⟨q1, q2⟩ := get_ev hq hx
  obtain ⟨p1, p2⟩ := get_ev hp q2
  rw [compA_get hx, compA_get hx, q1, p1, (get_ev hr p2).1]

theorem key_lt : ∀ p ∈ fi22FiveKeyPts, p < 3510 := by decide

theorem ne_of_difAt {p q r : ℕ} (hp : PP 3510 12 p) (hq : PP 3510 12 q) (hr : PP 3510 12 r)
    (h : difAt (fun x => ev p (ev q (ev r x))) (fun x => ev r (ev p (ev q x))) = true) :
    pe p * pe q * pe r ≠ pe r * (pe p * pe q) := fun e => by
  unfold difAt at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hne⟩ := h
  have hxl := key_lt x hx
  have R1 := rep_compA (rep_compA (rep_pe hp) (rep_pe hq)) (rep_pe hr)
  have R2 := rep_compA (rep_pe hr) (rep_compA (rep_pe hp) (rep_pe hq))
  rw [e] at R1
  have := (R1.apply hxl).trans (R2.apply hxl).symm
  rw [get3 hp hq hr hxl, get3' hp hq hr hxl] at this
  have hne' : (!(Nat.beq (ev p (ev q (ev r x))) (ev r (ev p (ev q x))))) = true := hne
  rw [this, Nat.beq_refl] at hne'
  exact Bool.noConfusion hne'

theorem mem_P_of {p : ℕ}
    (hp : PP 3510 12 p) (h : Fi22X.siftP p = true) : pe p ∈ fi22P := (mem_P hp).2 h

theorem u_mul_w_mem :
    fi22U * pe W ∈ fi22P := by
  obtain ⟨-, -, -, -, hc, hs⟩ := okW'
  have hU : Rep 3510 (unpack 3510 12 Fi22X.GO) fi22U := by
    rw [← Fi22X.go_eq]
    exact rep_fi22U
  have h := rep_compA hU (rep_pe pW)
  rw [Fi22X.comp_eq Fi22X.cnG pW.1] at h
  rw [← fi22InP_iff h, Fi22LabA.fi22InP_eq rfl hc]
  exact hs

theorem recHyp0 :
    RecHyp fi22P fi22R (pe Q1) (pe W) (pe A) (pe Q2) := by
  obtain ⟨-, -, hQc, hQ15, -, hQ1n, -⟩ := okQ'
  obtain ⟨-, hW2, hWn, hWs, -, -⟩ := okW'
  obtain ⟨-, hsQ1, hsQ2, hsA, hAQ1, hWQ1, hAW, hQ2W, hbc, -, -, -, -, hm1, hm2, hm3, hnab⟩ := ok0'
  obtain ⟨-, hnD, hcent⟩ := okD'
  have hx5 : pe Q1 ^ 5 = 1 := by
    rw [← pe_pw pQ1, ← pe_id]
    exact (pe_eq_iff (PP_pw pQ1 5) PP_id).2 hQ15
  have hx1 : pe Q1 ≠ 1 := by
    rw [← pe_id]
    exact ne_of pQ1 PP_id hQ1n
  have hwP : pe W ∉ fi22P := fun h => by
    rw [mem_P pW, hWs] at h
    exact Bool.noConfusion h
  have hUW := u_mul_w_mem
  have hxP := mem_P_of pQ1 hsQ1
  have hpA1 := PP_inv pA
  have hpQ2i := PP_inv pQ2
  refine
    { hPR := fi22P_le_R
      x5 := hx5
      x1 := hx1
      w2 := by
        rw [← pe_c pW pW, ← pe_id]
        exact (pe_eq_iff (PP_c pW pW) PP_id).2 hW2
      xP := hxP
      aP := mem_P_of pA hsA
      bP := mem_P_of pQ2 hsQ2
      wR := (mem_fi22R_iff _).2 (Or.inr hUW)
      wP := hwP
      Rw := fun g hg hgP => by
        rcases (mem_fi22R_iff g).1 hg with h | h
        · exact absurd h hgP
        · have := fi22P.mul_mem (fi22P.inv_mem hUW) h
          rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left] at this
      ax := comm_of pA pQ1 hAQ1
      bx := ?_
      wx := comm_of pW pQ1 hWQ1
      aw := comm_of pA pW hAW
      bw := comm_of pQ2 pW hQ2W
      bc := ?_
      dCard := card_D0
      dSimple := simple_D0
      nab := ?_
      cjA1 := ?_
      cjA2 := ?_
      cjB1 := ?_
      notD := ?_
      cent := ?_
      bound := card_centralizer_le_600 hxP (orderOf_eq_prime hx5 hx1) }
  · exact (comm_of pQ1 pQ2 hQc).symm
  · set G := Fi22X.c A (Fi22X.c (Fi22X.inv Q2) (Fi22X.inv Q2))
    set H' := Fi22X.c (Fi22X.inv Q2) (Fi22X.c (Fi22X.inv Q2) (Fi22X.c A (Fi22X.inv Q2)))
    have pG' : PP 3510 12 G := PP_c pA (PP_c hpQ2i hpQ2i)
    have pH' : PP 3510 12 H' := PP_c hpQ2i (PP_c hpQ2i (PP_c pA hpQ2i))
    have eG' : pe G = pe A * ((pe Q2)⁻¹ * (pe Q2)⁻¹) := by
      rw [pe_c pA (PP_c hpQ2i hpQ2i), pe_c hpQ2i hpQ2i, pe_inv pQ2]
    have eH' : pe H' = (pe Q2)⁻¹ * ((pe Q2)⁻¹ * (pe A * (pe Q2)⁻¹)) := by
      rw [pe_c hpQ2i (PP_c hpQ2i (PP_c pA hpQ2i)), pe_c hpQ2i (PP_c pA hpQ2i), pe_c pA hpQ2i,
        pe_inv pQ2]
    have e := (pe_eq_iff (PP_c pG' pH') (PP_c pQ2 (PP_c pH' pG'))).2 hbc
    rw [pe_c pG' pH', pe_c pQ2 (PP_c pH' pG'), pe_c pH' pG', eG', eH'] at e
    rw [commutatorElement_def]
    set B := pe Q2
    set A' := pe A
    set G1 := A' * (B⁻¹ * B⁻¹)
    set H1 := B⁻¹ * (B⁻¹ * (A' * B⁻¹))
    calc B = B * (H1 * G1) * (H1 * G1)⁻¹ := by group
      _ = G1 * H1 * (H1 * G1)⁻¹ := by rw [← e]
      _ = G1 * H1 * G1⁻¹ * H1⁻¹ := by group
  · rw [← pe_D1, ← pe_c pD1 pQ2, ← pe_c pQ2 pD1]
    exact ne_of (PP_c pD1 pQ2) (PP_c pQ2 pD1) hnab
  · have h := mem_D0_of_memE (PP_c pA (PP_c pD1 (PP_inv pA))) hm1
    rwa [pe_c pA (PP_c pD1 (PP_inv pA)), pe_c pD1 (PP_inv pA), pe_inv pA, pe_D1,
      ← mul_assoc] at h
  · have h := mem_D0_of_memE (PP_c pA (PP_c pQ2 (PP_inv pA))) hm2
    rwa [pe_c pA (PP_c pQ2 (PP_inv pA)), pe_c pQ2 (PP_inv pA), pe_inv pA, ← mul_assoc] at h
  · have h := mem_D0_of_memE (PP_c pQ2 (PP_c pD1 hpQ2i)) hm3
    rwa [pe_c pQ2 (PP_c pD1 hpQ2i), pe_c pD1 hpQ2i, pe_inv pQ2, pe_D1, ← mul_assoc] at h
  · intro e he hmem
    obtain ⟨i, hi, hT⟩ := mem_D0.1 hmem
    have hp : PP 3510 12 (Fi22X.c A (pwK (Fi22X.inv Q1) e)) := PP_c pA (PP_pw (PP_inv pQ1) e)
    have e1 : pe (Fi22X.c A (pwK (Fi22X.inv Q1) e)) = pe A * (pe Q1)⁻¹ ^ e := by
      rw [pe_c pA (PP_pw (PP_inv pQ1) e), pe_pw (PP_inv pQ1), pe_inv pQ1]
    rw [← e1] at hT
    have h := allN_spec' hnD he
    rw [memE_of hi ((pe_eq_iff (pT i hi) hp).1 hT |> Nat.eq_of_beq_eq_true)] at h
    exact Bool.noConfusion h
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := mem_D0.1 ht
    have h := allN_spec' hcent hi
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · left
      rw [← pe_D1, ← eG.1]
      exact ne_of_difAt pA (pT i hi) (pG 0 (by norm_num)) h
    · right
      exact ne_of_difAt pA (pT i hi) pQ2 h

theorem permsA_two (a b : Array ℕ) :
    permsA 3510 #[a, b] = ({permOfArr 3510 a, permOfArr 3510 b} : Set _) := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := hk
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp, rfl⟩

theorem permsA_four (a b c d : Array ℕ) :
    permsA 3510 #[a, b, c, d] =
      ({permOfArr 3510 a, permOfArr 3510 b, permOfArr 3510 c, permOfArr 3510 d} : Set _) := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk4 : k < 4 := hk
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp, rfl⟩
    · exact ⟨2, by simp, rfl⟩
    · exact ⟨3, by simp, rfl⟩

theorem q1Arr_eq : fi22FiveQ1Arr = unpack 3510 12 Q1 := fiveArr_eq (by norm_num)

theorem q2Arr_eq : fi22FiveQ2Arr = unpack 3510 12 Q2 := fiveArr_eq (by norm_num)

theorem w_eq : fi22FiveW = pe W := by
  unfold fi22FiveW
  rw [show fi22FiveWArr = unpack 3510 12 W from fiveArr_eq (by norm_num)]
  rfl

theorem line_eq (j : ℕ) : permOfArr 3510 (fi22FiveLineArr j) = lineE (pe Q1) (pe Q2) j := by
  unfold fi22FiveLineArr lineE
  split_ifs
  · rw [q1Arr_eq]
    rfl
  · rw [q2Arr_eq]
    rfl
  · apply permOfArr_eq_of_rep
    rw [q1Arr_eq, q2Arr_eq]
    exact rep_compA (rep_pe pQ1) (CFSG.Monster.B.Fischer.rep_powA (rep_pe pQ2) _)

theorem line_eq' (j : Fin 6) : fi22FiveLine j = lineE (pe Q1) (pe Q2) j := line_eq j

theorem lineK_one (a b : ℕ) : lineK a b 1 = b := rfl

theorem lineK_ge (a b j : ℕ) (hb : Nat.beq j 1 = false) : lineK a b j = Fi22X.c a (pwK b (j - 1)) := by
  unfold lineK
  rw [hb]
  rfl

theorem lineE_zero {G : Type*} [Group G] (x y : G) : lineE x y 0 = x := by
  unfold lineE
  rw [if_pos rfl]

theorem lineE_one {G : Type*} [Group G] (x y : G) : lineE x y 1 = y := by
  unfold lineE
  rw [if_neg (by norm_num), if_pos rfl]

theorem lineK_facts {j : ℕ} (h1 : 1 ≤ j) :
    PP 3510 12 (lineK Q1 Q2 j) ∧ pe (lineK Q1 Q2 j) = lineE (pe Q1) (pe Q2) j := by
  rcases Nat.lt_or_ge j 2 with hj | hj
  · obtain rfl : j = 1 := by omega
    rw [lineK_one, lineE_one]
    exact ⟨pQ2, rfl⟩
  · have hb : Nat.beq j 1 = false := by
      cases e : Nat.beq j 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) (by omega)
    rw [lineK_ge Q1 Q2 j hb]
    refine ⟨PP_c pQ1 (PP_pw pQ2 _), ?_⟩
    rw [pe_c pQ1 (PP_pw pQ2 _), pe_pw pQ2]
    unfold lineE
    rw [if_neg (by omega), if_neg (by omega)]

@[expose] noncomputable def hT (j : ℕ) : Equiv.Perm (Fin 3510) := permOfArr 3510 (fi22FiveHArr j)

theorem hArr_facts {j : ℕ} (hj1 : 1 ≤ j) (hj : j < 6) :
    fi22FiveHArr j = unpack 3510 12 (H j) ∧ PP 3510 12 (H j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  refine ⟨?_, PP_of_isP (okH' (by omega)).1⟩
  unfold fi22FiveHArr
  rw [if_neg (by omega)]
  exact fiveArr_eq (by omega)

theorem validH {j : ℕ} (hj : j < 6) : validA 3510 (fi22FiveHArr j) = true := by
  rcases Nat.eq_zero_or_pos j with rfl | h0
  · have e : fi22FiveHArr 0 = unpack 3510 12 idP := by
      unfold fi22FiveHArr
      rw [if_pos rfl, idP, ← idA_eq hsz]
    rw [e]
    exact CFSG.KC.B3S3K.validA_of (CFSG.KC.Misc.ArrEnum.permB_of_pp PP_id)
  · rw [(hArr_facts h0 hj).1]
    exact CFSG.KC.B3S3K.validA_of (CFSG.KC.Misc.ArrEnum.permB_of_pp (hArr_facts h0 hj).2)

theorem trans_facts (j : Fin 6) :
    hT j ∈ fi22P ∧ hT j * fi22FiveLine j = fi22FiveLine 0 * hT j ∧ hT j * pe W = pe W * hT j := by
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
  · have e : hT j = 1 := by
      unfold hT
      rw [h0]
      apply permOfArr_eq_of_rep
      unfold fi22FiveHArr
      rw [if_pos rfl]
      exact rep_idA
    have ej : j = 0 := Fin.ext h0
    rw [e, ej]
    exact ⟨fi22P.one_mem, by group, by group⟩
  · obtain ⟨ea, pH⟩ := hArr_facts h0 j.2
    obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = k + 1 := ⟨j - 1, by omega⟩
    obtain ⟨-, hs, hc, hw⟩ := okH' (j := k) (by omega)
    rw [← hk] at hs hc hw
    have e : hT j = pe (H j) := by
      unfold hT
      rw [ea]
      rfl
    obtain ⟨pL, eL⟩ := lineK_facts h0
    rw [e, line_eq', line_eq', Fin.val_zero, lineE_zero]
    refine ⟨(mem_P pH).2 hs, ?_, comm_of pH pW hw⟩
    have h := (pe_eq_iff (PP_c pH pL) (PP_c pQ1 pH)).2 hc
    rw [pe_c pH pL, pe_c pQ1 pH, eL] at h
    exact h

@[expose] noncomputable def φ (j : ℕ) : Equiv.Perm (Fin 3510) ≃* Equiv.Perm (Fin 3510) :=
  MulAut.conj (hT j)⁻¹

theorem φ_apply (j : ℕ) (g : Equiv.Perm (Fin 3510)) : φ j g = (hT j)⁻¹ * g * hT j := by
  rw [φ, MulAut.conj_apply, inv_inv]

theorem cgens_eq (j : Fin 6) :
    permsA 3510 (fi22FiveCGenArrs j) =
      ({fi22FiveLine j, φ j (pe A), φ j (pe Q2), pe W} : Set _) := by
  have hv := validH j.2
  have e1 : permOfArr 3510 (conjInvA 3510 (fi22FiveHArr j) fi22FiveAArr) = φ j (pe A) := by
    rw [φ_apply]
    apply permOfArr_eq_of_rep
    rw [aArr_eq]
    exact rep_conjInvA hv (rep_pe pA)
  have e2 : permOfArr 3510 (conjInvA 3510 (fi22FiveHArr j) fi22FiveQ2Arr) = φ j (pe Q2) := by
    rw [φ_apply]
    apply permOfArr_eq_of_rep
    rw [q2Arr_eq]
    exact rep_conjInvA hv (rep_pe pQ2)
  unfold fi22FiveCGenArrs
  rw [permsA_four, e1, e2, ← w_eq]
  rfl

theorem recHyp
    (j : Fin 6) :
    RecHyp fi22P fi22R (fi22FiveLine j) (pe W) (φ j (pe A)) (φ j (pe Q2)) := by
  obtain ⟨hhP, hhx, hhw⟩ := trans_facts j
  have H0 := recHyp0
  have hP : ∀ g, φ j g ∈ fi22P ↔ g ∈ fi22P := fun g => by
    rw [φ_apply]
    constructor
    · intro hg
      have := fi22P.mul_mem (fi22P.mul_mem hhP hg) (fi22P.inv_mem hhP)
      have e : hT j * ((hT j)⁻¹ * g * hT j) * (hT j)⁻¹ = g := by group
      rwa [e] at this
    · intro hg
      exact fi22P.mul_mem (fi22P.mul_mem (fi22P.inv_mem hhP) hg) hhP
  have e0 : fi22FiveLine 0 = pe Q1 := by
    rw [line_eq', Fin.val_zero, lineE_zero]
  have hx : φ j (pe Q1) = fi22FiveLine j := by
    rw [φ_apply, ← e0, mul_assoc, ← hhx]
    group
  have hw : φ j (pe W) = pe W := by
    rw [φ_apply, mul_assoc, ← hhw]
    group
  have hb : Nat.card (Subgroup.centralizer {φ j (pe Q1)} ⊓ fi22P : Subgroup _) ≤ 600 :=
    card_centralizer_le_600 ((hP _).2 H0.xP)
      (by rw [← H0.orderOf_x]; exact orderOf_injective (φ j).toMonoidHom (φ j).injective _)
  have := H0.map (φ j) hP hw hb
  rwa [hx] at this

theorem facts :
    (fi22FiveQ ≤ fi22P ∧ CFSG.IsElementaryAbelian 5 fi22FiveQ ∧ Nat.card fi22FiveQ = 25 ∧
      ∃ S : Sylow 5 fi22P, (S : Subgroup fi22P) = fi22FiveQ.subgroupOf fi22P) ∧
    ({H : Subgroup (Equiv.Perm (Fin 3510)) | H ≤ fi22FiveQ ∧ Nat.card H = 5} =
        Set.range (fun i : Fin 6 => Subgroup.zpowers (fi22FiveLine i)) ∧
      Function.Injective (fun i : Fin 6 => Subgroup.zpowers (fi22FiveLine i))) ∧
    (fi22FiveW ∈ fi22R ∧ fi22FiveW ∉ fi22P ∧ orderOf fi22FiveW = 2) ∧
    ∀ i : Fin 6,
      fi22FiveC i = Subgroup.centralizer {fi22FiveLine i} ⊓ fi22R ∧
      Nat.card (fi22FiveC i) = 1200 ∧
      fi22FiveC i ⊓ fi22P = Subgroup.centralizer {fi22FiveLine i} ⊓ fi22P ∧
      Nat.card (fi22FiveC i ⊓ fi22P : Subgroup (Equiv.Perm (Fin 3510))) = 600 ∧
      fi22FiveD i ≤ fi22P ∧ IsSimpleGroup (fi22FiveD i) ∧
      (∃ g ∈ fi22FiveD i, ∃ h ∈ fi22FiveD i, g * h ≠ h * g) ∧ Nat.card (fi22FiveD i) = 60 ∧
      fi22FiveW ∈ (Subgroup.center (fi22FiveC i)).map (fi22FiveC i).subtype ∧
      Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ fi22FiveC i =
        Subgroup.zpowers (fi22FiveLine i) ⊔ Subgroup.zpowers fi22FiveW ∧
      Subgroup.zpowers (fi22FiveLine i) ⊓ Subgroup.zpowers fi22FiveW = ⊥ ∧
      Commute (fi22FiveLine i) fi22FiveW ∧
      Nat.card (Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ fi22FiveC i :
        Subgroup (Equiv.Perm (Fin 3510))) = 10 ∧
      Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ (fi22FiveC i ⊓ fi22P) =
        Subgroup.zpowers (fi22FiveLine i) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, -, hQc, hQ15, hQ25, hQ1n, hQn⟩ := okQ'
  have H0 := recHyp0
  have hD : PlaneData (pe Q1) (pe Q2) :=
    plane_of H0.x5 (by
        rw [← pe_pw pQ2, ← pe_id]
        exact (pe_eq_iff (PP_pw pQ2 5) PP_id).2 hQ25)
      (comm_of pQ1 pQ2 hQc) H0.x1 (fun e he h => by
        have := allN_spec' hQn he
        rw [← pe_pw pQ1] at h
        rw [(pe_eq_iff pQ2 (PP_pw pQ1 e)).1 h] at this
        exact Bool.noConfusion this)
  have hQ : fi22FiveQ = Subgroup.closure ({pe Q1, pe Q2} : Set _) := by
    unfold fi22FiveQ fi22FiveQGenArrs
    rw [permsA_two, q1Arr_eq, q2Arr_eq]
    rfl
  obtain ⟨hEA, hcard, -⟩ := hD.closure_facts
  have hQP : fi22FiveQ ≤ fi22P := by
    rw [hQ, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [H0.xP, H0.bP]
  have hcQ : Nat.card fi22FiveQ = 25 := by
    rw [hQ, hcard]
    norm_num
  have hline : ∀ j : Fin 6, fi22FiveLine j ∈ fi22FiveQ := fun j => by
    rw [line_eq', hQ]
    have h1 : pe Q1 ∈ Subgroup.closure ({pe Q1, pe Q2} : Set _) := Subgroup.subset_closure (by simp)
    have h2 : pe Q2 ∈ Subgroup.closure ({pe Q1, pe Q2} : Set _) := Subgroup.subset_closure (by simp)
    unfold lineE
    split_ifs
    exacts [h1, h2, Subgroup.mul_mem _ h1 (Subgroup.pow_mem _ h2 _)]
  have hpow : ∀ j : Fin 6, fi22FiveLine j ^ 5 = 1 := fun j => by
    rw [line_eq', lineE_pow hD.comm hD.x_pow hD.y_pow, Nat.mul_mod_right, Nat.mul_mod_right,
      pow_zero, pow_zero, one_mul]
  have hne : ∀ j : Fin 6, fi22FiveLine j ≠ 1 := fun j h => by
    rw [line_eq'] at h
    have e := lineE_pow hD.comm hD.x_pow hD.y_pow (j : ℕ) 1
    rw [pow_one, h] at e
    have e' : pe Q1 ^ 0 * pe Q2 ^ 0 = pe Q1 ^ (1 * (lineExp j).1 % 5) *
        pe Q2 ^ (1 * (lineExp j).2 % 5) := by
      rw [pow_zero, pow_zero, one_mul]
      exact e
    obtain ⟨h1, h2⟩ := planeMap_inj hD (by norm_num) (by norm_num) (Nat.mod_lt _ (by norm_num))
      (Nat.mod_lt _ (by norm_num)) e'
    have hj := j.2
    revert h1 h2
    generalize (j : ℕ) = k at hj
    interval_cases k <;> decide
  have hEl : CFSG.IsElementaryAbelian 5 fi22FiveQ := by
    rw [hQ]
    obtain ⟨h1, h2⟩ := hEA
    exact
      { toIsMulCommutative := h1
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun g =>
          Subtype.ext (h2 _ g.2) }
  refine ⟨⟨hQP, hEl, hcQ, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, fun i => ?_⟩
  · have hfac : (Nat.card fi22P).factorization 5 = 2 := by
      rw [card_fi22P, show (64561751654400 : ℕ) = 5 ^ 2 * 2582470066176 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    have hc : Nat.card (fi22FiveQ.subgroupOf fi22P) = 5 ^ (Nat.card fi22P).factorization 5 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hcQ, hfac]
      norm_num
    exact ⟨Sylow.ofCard _ hc, rfl⟩
  · apply prime_subgroups_eq_range fi22FiveLine hline hne hpow
    · intro g hg hg1
      rw [hQ] at hg
      obtain ⟨j, hj, k, e⟩ := lines_cover hD hg hg1
      exact ⟨⟨j, hj⟩, k, by rw [line_eq']; exact e⟩
    · intro j j' k hk h
      rw [line_eq', line_eq'] at h
      exact Fin.ext (lines_dist hD j.2 j'.2 hk h)
  · rw [w_eq]
    exact H0.wR
  · rw [w_eq]
    exact H0.wP
  · rw [w_eq]
    exact H0.orderOf_w
  · have hF := (recHyp i).facts
    have hC : fi22FiveC i =
        Subgroup.closure ({fi22FiveLine i, φ i (pe A), φ i (pe Q2), pe W} : Set _) := by
      unfold fi22FiveC
      rw [cgens_eq]
    rw [← hC, ← w_eq] at hF
    exact hF

end CertificateChecks.KernelSpor.Fv8124
