module

public import Certificates.Kernel.Sporadic.Fi22.L17337K
public import Certificates.Kernel.Sporadic.Fi22.Five8124G
public import CFSG.Certificates.Kernel.Fi22Cent.WordsSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.L17337

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.Fi22Cent
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fv8124
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.PartOne
open CFSG.HardMathSupport.Dickson.I271.TabFi22Cent (lArrs xArr relsU43 arr)

theorem letF_0f (a b ai bi y : ℕ) : letF a b ai bi (0, false) y = ev ai y := rfl
theorem letF_0t (a b ai bi y : ℕ) : letF a b ai bi (0, true) y = ev a y := rfl
theorem letF_1f (a b ai bi y : ℕ) : letF a b ai bi (1, false) y = ev bi y := rfl
theorem letF_1t (a b ai bi y : ℕ) : letF a b ai bi (1, true) y = ev b y := rfl

theorem letF_spec {a b ai bi : ℕ} {G H : Equiv.Perm (Fin 3510)}
    (ha : ∀ y : Fin 3510, ev a y = G y) (hb : ∀ y : Fin 3510, ev b y = H y)
    (hai : ∀ y : Fin 3510, ev ai y = G⁻¹ y) (hbi : ∀ y : Fin 3510, ev bi y = H⁻¹ y) :
    ∀ (i : Fin 2) (e : Bool) (y : Fin 3510),
      letF a b ai bi (i, e) y = ((cond e (![G, H] i) (![G, H] i)⁻¹ y : Fin 3510) : ℕ) := by
  rw [Fin.forall_fin_two, Bool.forall_bool, Bool.forall_bool]
  refine ⟨⟨fun y => ?_, fun y => ?_⟩, ⟨fun y => ?_, fun y => ?_⟩⟩
  · rw [letF_0f, cond_false, Matrix.cons_val_zero, hai]
  · rw [letF_0t, cond_true, Matrix.cons_val_zero, ha]
  · rw [letF_1f, cond_false, Matrix.cons_val_one, Matrix.cons_val_fin_one, hbi]
  · rw [letF_1t, cond_true, Matrix.cons_val_one, Matrix.cons_val_fin_one, hb]

theorem letter_mem {G H : Equiv.Perm (Fin 3510)} {P : Subgroup (Equiv.Perm (Fin 3510))}
    (hG : G ∈ P) (hH : H ∈ P) : ∀ (i : Fin 2) (e : Bool), cond e (![G, H] i) (![G, H] i)⁻¹ ∈ P := by
  rw [Fin.forall_fin_two, Bool.forall_bool, Bool.forall_bool]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [cond_false, Matrix.cons_val_zero]
    exact P.inv_mem hG
  · rw [cond_true, Matrix.cons_val_zero]
    exact hG
  · rw [cond_false, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact P.inv_mem hH
  · rw [cond_true, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact hH

theorem ev_pe {p : ℕ} (hp : PP 3510 12 p) (y : Fin 3510) : ev p y = pe p y :=
  (pe_apply hp y).symm

theorem ev_pe_inv {p : ℕ} (hp : PP 3510 12 p) (y : Fin 3510) : ev (Fi22X.inv p) y = (pe p)⁻¹ y := by
  rw [← pe_inv hp]
  exact (pe_apply (PP_inv hp) y).symm

theorem fix_base
    {G : Equiv.Perm (Fin 3510)} (hG : G ∈ fi22P)
    (h : ∀ p ∈ [0, 1, 2, 3, 6, 4], ∀ hp : p < 3510, G ⟨p, hp⟩ = ⟨p, hp⟩) : G = 1 := by
  refine fi22Chain.eq_one_of_fixes_base fi22Chain_valid.1 hG fun i => ?_
  obtain ⟨i, hi⟩ := i
  change i < 6 at hi
  interval_cases i
  · exact h 0 (by simp) (by norm_num)
  · exact h 1 (by simp) (by norm_num)
  · exact h 2 (by simp) (by norm_num)
  · exact h 3 (by simp) (by norm_num)
  · exact h 6 (by simp) (by norm_num)
  · exact h 4 (by simp) (by norm_num)

theorem okB' : (allN 8 fun j => Nat.beq (Fi22L17.S j) (Fi22LT.F (Nat.add 2 j))) = true ∧
    (allN 7 fun t => Nat.beq LB[t]! (pg 12 (mask 12) Fi22L17.BP t)) = true :=
  (bAnd_iff _ _).1 okB

theorem arr_eq {k : ℕ} (hk : k < 10) : arr k = unpack 3510 12 (Fi22LT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound Fi22LT.all k hk
  rw [← Fi22LT.eq] at h
  exact h

theorem lArrs_size : (lArrs ()).size = 8 := by
  simp [CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.lArrs]

theorem lArrs_get {j : ℕ} (hj : j < 8) : (lArrs ())[j]! = arr (2 + j) := by
  rw [getElem!_pos _ j (by rw [lArrs_size]; exact hj)]
  simp only [CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.lArrs, Array.getElem_ofFn]

theorem lArrs_eq {j : ℕ} (hj : j < 8) : (lArrs ())[j]! = unpack 3510 12 (Fi22L17.S j) := by
  rw [lArrs_get hj, arr_eq (by omega), Nat.eq_of_beq_eq_true (allN_spec' okB'.1 hj)]
  rfl

theorem binds : Binds 3510 12 Fi22L17.S 8 7 Fi22L17.BP (lArrs ()) LB :=
  ⟨by norm_num, by norm_num, by norm_num, lArrs_size, fun j hj => lArrs_eq hj, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec' okB'.2 ht)⟩

theorem okP' {j : ℕ} (hj : j < 8) : isP (Fi22L17.S j) = true ∧ Fi22X.siftP (Fi22L17.S j) = true := by
  have h := allN_spec' okP hj
  rw [Fv8124.strictB_eq, Bool.and_eq_true] at h
  exact h

theorem pS {j : ℕ} (hj : j < 8) : PP 3510 12 (Fi22L17.S j) := PP_of_isP (okP' hj).1

theorem pS_mem {j : ℕ} (hj : j < 8) :
    pe (Fi22L17.S j) ∈ fi22P :=
  (mem_P (pS hj)).2 (okP' hj).2

theorem sep :
    Sep 3510 (lArrs ()) LB := by
  intro G hG hfix
  have hle : Subgroup.closure {g : Equiv.Perm (Fin 3510) |
      ∃ j < (lArrs ()).size, permOfArr 3510 (lArrs ())[j]! = g} ≤ fi22P := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    rw [lArrs_size] at hj
    rw [lArrs_eq hj]
    exact pS_mem hj
  refine fix_base (hle hG) fun p hp hp' => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hfix 3 (by decide) hp'
  · exact hfix 4 (by decide) hp'
  · exact hfix 1 (by decide) hp'
  · exact hfix 2 (by decide) hp'
  · exact hfix 5 (by decide) hp'
  · exact hfix 6 (by decide) hp'

theorem chain :
    caseChainOK2P 3510 (lArrs ()) LB (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 8 Fi22LD.D)
      (lArrs ())[0]! (lArrs ())[1]! = true := by
  have h := rawChainTK_sound binds Fi22L17.head Fi22L17.tl Fi22L17.hst sep Fi22L17.hs
    (chunks := 1) (by norm_num)
  unfold caseChainOK2P
  rw [h, eqA_self, eqA_self]
  rfl

theorem pA : PP 3510 12 A := pS (j := 0) (by norm_num)
theorem pB : PP 3510 12 B := pS (j := 1) (by norm_num)

theorem rep_A : Rep 3510 (lArrs ())[0]! (pe A) := by
  rw [lArrs_eq (by norm_num)]
  exact rep_pe pA

theorem rep_B : Rep 3510 (lArrs ())[1]! (pe B) := by
  rw [lArrs_eq (by norm_num)]
  exact rep_pe pB

theorem card_L :
    Nat.card (Subgroup.closure {pe A, pe B}) = 3265920 := by
  have e : (([19, 2, 3, 0, 1, 6, 4] : List (Fin 3510)).map Fin.val).toArray = LB := by decide
  have hnodup : ([19, 2, 3, 0, 1, 6, 4] : List (Fin 3510)).Nodup := by decide
  have hc := chain
  rw [← e] at hc
  have h := card_closure_two_of_chainOK (n := 3510) (by norm_num) (by rw [lArrs_size]; norm_num)
    hnodup rep_A rep_B hc
  rw [h, e, rawOrbitSizesTK_sound binds Fi22L17.head Fi22L17.tl, orbits]
  rfl

theorem okA' : isP X = true ∧ Nat.beq (ev A 0) 0 = true ∧ Nat.beq (ev A 1) 1 = true ∧
    Nat.beq (ev B 0) 0 = true ∧ Nat.beq (ev B 1) 1 = true ∧
    Nat.beq (Fi22X.c A X) (Fi22X.c X A) = true ∧ Nat.beq (Fi22X.c B X) (Fi22X.c X B) = true := by
  have h := okA
  simp only [Fv8124.strictB_eq, chkA, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem pX : PP 3510 12 X := PP_of_isP okA'.1

theorem mem_A : pe A ∈ fi22P :=
  pS_mem (j := 0) (by norm_num)
theorem mem_B : pe B ∈ fi22P :=
  pS_mem (j := 1) (by norm_num)

theorem xArr_eq : xArr () = unpack 3510 12 X := arr_eq (k := 1) (by norm_num)

theorem comm_x {x : Equiv.Perm (Fin 3510)} (hx : ∀ v : Fin 3510, (xArr ())[(v : ℕ)]! = x v) :
    pe A * x = x * pe A ∧ pe B * x = x * pe B := by
  have e : x = pe X := by
    rw [← CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep hx, xArr_eq]
    rfl
  rw [e]
  exact ⟨comm_of pA pX okA'.2.2.2.2.2.1, comm_of pB pX okA'.2.2.2.2.2.2⟩

theorem okR' : chkR A B (Fi22X.inv A) (Fi22X.inv B) = true := by
  have h := okR
  simp only [Fv8124.strictB_eq] at h
  exact h

theorem rels :
    ∀ w ∈ relsU43, (w.map fun l => cond l.2 (![pe A, pe B] l.1) (![pe A, pe B] l.1)⁻¹).prod = 1 := by
  intro w hw
  have h := List.all_eq_true.1 okR' w hw
  refine fix_base (Subgroup.list_prod_mem _ fun g hg => ?_) fun p hp hp' => ?_
  · obtain ⟨l, -, rfl⟩ := List.mem_map.1 hg
    exact letter_mem mem_A mem_B l.1 l.2
  · have hq := Nat.eq_of_beq_eq_true (List.all_eq_true.1 h p hp)
    have hf := letF_spec (ev_pe pA) (ev_pe pB) (ev_pe_inv pA) (ev_pe_inv pB)
    rw [wAt_eq (g := fun l => cond l.2 (![pe A, pe B] l.1) (![pe A, pe B] l.1)⁻¹)
      (fun l y => hf l.1 l.2 y) w ⟨p, hp'⟩] at hq
    exact Fin.ext hq

theorem tie_A : ∀ v : Fin 3510, ((lArrs ())[0]!)[(v : ℕ)]! = pe A v := rep_A
theorem tie_B : ∀ v : Fin 3510, ((lArrs ())[1]!)[(v : ℕ)]! = pe B v := rep_B

theorem fixA0 : pe A 0 = 0 := Fin.ext ((pe_apply pA 0).trans (Nat.eq_of_beq_eq_true okA'.2.1))
theorem fixA1 : pe A 1 = 1 :=
  Fin.ext ((pe_apply pA 1).trans (Nat.eq_of_beq_eq_true okA'.2.2.1))
theorem fixB0 : pe B 0 = 0 :=
  Fin.ext ((pe_apply pB 0).trans (Nat.eq_of_beq_eq_true okA'.2.2.2.1))
theorem fixB1 : pe B 1 = 1 :=
  Fin.ext ((pe_apply pB 1).trans (Nat.eq_of_beq_eq_true okA'.2.2.2.2.1))

theorem facts :
    ∃ a b : Equiv.Perm (Fin 3510),
      (∀ v : Fin 3510, ((lArrs ())[0]!)[(v : ℕ)]! = a v) ∧
      (∀ v : Fin 3510, ((lArrs ())[1]!)[(v : ℕ)]! = b v) ∧
      Nat.card (Subgroup.closure {a, b}) = 3265920 ∧ a ∈ fi22P ∧ b ∈ fi22P ∧
      a 0 = 0 ∧ a 1 = 1 ∧ b 0 = 0 ∧ b 1 = 1 ∧
      (∀ x : Equiv.Perm (Fin 3510), (∀ v : Fin 3510, (xArr ())[(v : ℕ)]! = x v) →
        a * x = x * a ∧ b * x = x * b) ∧
      ∀ w ∈ relsU43, (w.map fun l => cond l.2 (![a, b] l.1) (![a, b] l.1)⁻¹).prod = 1 := by
  exact ⟨pe A, pe B, tie_A, tie_B, card_L, mem_A, mem_B, fixA0, fixA1, fixB0, fixB1,
    fun _ hx => comm_x hx, rels⟩

end CertificateChecks.KernelSpor.L17337

end
