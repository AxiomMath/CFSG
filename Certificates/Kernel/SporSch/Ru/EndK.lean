module

public import Certificates.Kernel.SporSch.Ru.EndChecks
public import Certificates.Kernel.SporSch.Ru.EndChain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuEndK
public import CFSG.Certificates.Kernel.SporSch.ChainKClasses
public import CFSG.Certificates.Kernel.Spor.RawSound
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuEnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch CFSG.KS.SporSch.MOC
open CFSG.ComponentClassification.RankTwoSporadic.Ru CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.RankTwoSporadic.Endgame CFSG.Sporadic.Schreier
open CertificateChecks.KernelSporSch
open scoped commutatorElement

theorem prep_of {P PI : Nat} (h : permOK 4060 12 (mask 12) (4060 * 12) P PI = true) :
    PRep 4060 12 P (permOfArr 4060 (unpack 4060 12 P)) ∧
      PRep 4060 12 PI (permOfArr 4060 (unpack 4060 12 P))⁻¹ := by
  have hr := rep_permOfArr (isInvA_unpack h)
  exact ⟨prep_of_rep hr.1, prep_of_rep hr.2⟩

theorem ap {P : Nat} {x : Equiv.Perm (Fin 4060)} (h : PRep 4060 12 P x) (p : Fin 4060) :
    ((x p : Fin 4060) : ℕ) = fv P p := (h p).symm

theorem ext4060 {x y : Equiv.Perm (Fin 4060)}
    (h : ∀ p : Fin 4060, ((x p : Fin 4060) : ℕ) = y p) : x = y :=
  Equiv.ext fun p => Fin.ext (h p)

theorem beq_eq {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem ne_spec {a b : Nat} (h : ne a b = true) : a ≠ b := by
  intro e
  subst e
  unfold ne at h
  rw [Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem imageList_of_rep {n : Nat} {t : Array Nat} {g : Equiv.Perm (Fin n)} (ht : t.size = n)
    (h : Rep n t g) : CFSG.Monster.B.Mathieu.imageList g = t.toList := by
  apply List.ext_getElem
  · simp [CFSG.Monster.B.Mathieu.imageList, ht]
  · intro i h1 h2
    have hi : i < n := by simpa [CFSG.Monster.B.Mathieu.imageList] using h1
    simp only [CFSG.Monster.B.Mathieu.imageList, List.getElem_ofFn, Array.getElem_toList]
    rw [← h.apply hi, getElem!_pos t i (by omega)]

section Generic

variable {P Q PI QI : Nat} {x y : Equiv.Perm (Fin 4060)}

theorem sq_of (hx : PRep 4060 12 P x) (h : ∀ p : Fin 4060, Nat.beq (fv P (fv P p)) p = true) :
    x * x = 1 :=
  ext4060 fun p => by
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, ap hx]
    exact beq_eq (h p)

theorem comm_of (hx : PRep 4060 12 P x) (hy : PRep 4060 12 Q y)
    (h : ∀ p : Fin 4060, Nat.beq (fv P (fv Q p)) (fv Q (fv P p)) = true) : x * y = y * x :=
  ext4060 fun p => by
    simp only [Equiv.Perm.mul_apply, ap hx, ap hy]
    exact beq_eq (h p)

theorem fpf_of (hx : PRep 4060 12 P x) (h : ∀ p : Fin 4060, ne (fv P p) p = true) (p : Fin 4060) :
    x p ≠ p := fun e => by
  have := congrArg Fin.val e
  rw [ap hx] at this
  exact ne_spec (h p) this

theorem fpf2_of (hx : PRep 4060 12 P x) (hy : PRep 4060 12 Q y)
    (h : ∀ p : Fin 4060, ne (fv P (fv Q p)) p = true) (p : Fin 4060) : (x * y) p ≠ p := fun e => by
  have := congrArg Fin.val e
  rw [Equiv.Perm.mul_apply, ap hx, ap hy] at this
  exact ne_spec (h p) this

variable {b e e' : Equiv.Perm (Fin 4060)}

theorem conjComm_of (hb : PRep 4060 12 B b) (hbi : PRep 4060 12 BI b⁻¹) (he : PRep 4060 12 P e)
    (he' : PRep 4060 12 Q e') (h : ∀ p : Fin 4060, cB P Q p = true) :
    e * (b⁻¹ * e' * b) = b⁻¹ * e' * b * e :=
  ext4060 fun p => by
    simp only [Equiv.Perm.mul_apply, ap hb, ap hbi, ap he, ap he']
    exact beq_eq (h p)

theorem cC_eq (hb : PRep 4060 12 B b) (hbi : PRep 4060 12 BI b⁻¹) (he : PRep 4060 12 A0 e)
    (p : Fin 4060) : (((b⁻¹ * e * b) p : Fin 4060) : ℕ) = cC p := by
  simp only [Equiv.Perm.mul_apply, ap hb, ap hbi, ap he]
  rfl

theorem conjNe_of (hb : PRep 4060 12 B b) (hbi : PRep 4060 12 BI b⁻¹) (he : PRep 4060 12 A0 e)
    {f : Equiv.Perm (Fin 4060)} {F : Nat → Nat} (hf : ∀ p : Fin 4060, ((f p : Fin 4060) : ℕ) = F p)
    (h : ∃ p < 4060, ne (cC p) (F p) = true) : b⁻¹ * e * b ≠ f := fun hc => by
  obtain ⟨p, hp, hn⟩ := h
  have := congrArg (fun g : Equiv.Perm (Fin 4060) => ((g ⟨p, hp⟩ : Fin 4060) : ℕ)) hc
  rw [cC_eq hb hbi he, hf] at this
  exact ne_spec hn this

theorem comm_eq {C : Nat} {c : Equiv.Perm (Fin 4060)} (hx : PRep 4060 12 P x)
    (hxi : PRep 4060 12 PI x⁻¹) (hy : PRep 4060 12 Q y) (hyi : PRep 4060 12 QI y⁻¹)
    (hc : PRep 4060 12 C c) (h : ∀ p : Fin 4060, Nat.beq (fv C p) (cm P Q PI QI p) = true) :
    c = ⁅x, y⁆ :=
  ext4060 fun p => by
    rw [commutatorElement_def]
    simp only [Equiv.Perm.mul_apply, ap hx, ap hy, ap hxi, ap hyi, ap hc]
    exact beq_eq (h p)

theorem top_eq (hx : PRep 4060 12 P x) (hxi : PRep 4060 12 PI x⁻¹) (hy : PRep 4060 12 Q y)
    (hyi : PRep 4060 12 QI y⁻¹) (hb : PRep 4060 12 B b) (hbi : PRep 4060 12 BI b⁻¹)
    (he : PRep 4060 12 A0 e)
    (h : ∀ p : Fin 4060, Nat.beq (cm P Q PI QI p) (fv A0 (cC p)) = true) :
    ⁅x, y⁆ = e * (b⁻¹ * e * b) :=
  ext4060 fun p => by
    rw [commutatorElement_def, Equiv.Perm.mul_apply e, ap he, cC_eq hb hbi he]
    simp only [Equiv.Perm.mul_apply, ap hx, ap hy, ap hxi, ap hyi]
    exact beq_eq (h p)

theorem lab_of {L : Nat} {l : Equiv.Perm (Fin 4060)} (hl : PRep 4060 12 L l) {i : Nat}
    (h : ∀ p : Fin 4060, Nat.beq (fv LAB (fv L p)) (sigK i (fv LAB p)) = true) (p : Fin 4060) :
    fv LAB ((l p : Fin 4060) : ℕ) = sigK i (fv LAB p) := by
  rw [ap hl]
  exact beq_eq (h p)

theorem fix_of {Z : Nat} {z : Equiv.Perm (Fin 4060)} (hZ : PRep 4060 12 Z z)
    (h : anyN 4060 (fun p => bIf(Nat.beq (fv Z (fv Z p)) p,
      bIf(Nat.beq (fv LAB (fv Z p)) (fv LAB p), Nat.beq (fv Z p) p, true), true)) = true)
    (hz2 : z ^ 2 = 1) (hlab : ∀ p : Fin 4060, fv LAB ((z p : Fin 4060) : ℕ) = fv LAB p) :
    ∃ p, z p = p := by
  obtain ⟨p, hp, hw⟩ := anyN_spec h
  refine ⟨⟨p, hp⟩, Fin.ext ?_⟩
  have e2 : Nat.beq (fv Z (fv Z p)) p = true := by
    have := congrArg (fun f : Equiv.Perm (Fin 4060) => ((f ⟨p, hp⟩ : Fin 4060) : ℕ)) hz2
    simp only [sq, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, ap hZ] at this
    rw [this, Nat.beq_refl]
  have e3 : Nat.beq (fv LAB (fv Z p)) (fv LAB p) = true := by
    have := hlab ⟨p, hp⟩
    rw [ap hZ] at this
    rw [this, Nat.beq_refl]
  rw [e2, e3] at hw
  rw [ap hZ]
  exact beq_eq hw

end Generic

theorem pFacts : permOK 4060 12 (mask 12) (4060 * 12) A0 A0I = true ∧
    permOK 4060 12 (mask 12) (4060 * 12) B BI = true ∧
    permOK 4060 12 (mask 12) (4060 * 12) R RI = true ∧
    (∀ i < 8, permOK 4060 12 (mask 12) (4060 * 12) (X i) (XI i) = true) ∧
    ∀ i < 6, permOK 4060 12 (mask 12) (4060 * 12) (Y i) (YI i) = true := by
  have h := pOK
  unfold pK at h
  simp only [CFSG.KS.bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, CFSG.KS.allN_spec h4, CFSG.KS.allN_spec h5⟩

theorem field_get3 {j : Nat} (hj : j < 18) : (ruField4060 3)[j]! = ruArr4060 (15 + j) := by
  rw [ruField4060, getElem!_pos _ j (by simpa [ruLines4060] using hj), Array.getElem_ofFn]
  rfl

theorem field_get5 {j : Nat} (hj : j < 6) : (ruField4060 5)[j]! = ruArr4060 (39 + j) := by
  rw [ruField4060, getElem!_pos _ j (by simpa [ruLines4060] using hj), Array.getElem_ofFn]
  rfl

theorem bindsJ : Binds 4060 12 RuJS.S 18 4 RuJS.BP (ruField4060 3) (ruBaseArr 4060 ruJoinBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [ruField4060, ruLines4060],
    fun j hj => by
      have e : RuJS.S j = RuT4060.L (15 + j) := Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec sJ j hj)
      rw [field_get3 hj, e]
      exact RuLines.row4060 (by omega),
    by simp [ruBaseArr, ruJoinBase], fun t ht => Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec bJ t ht)⟩

theorem inPA_of {P PI : Nat} (hp : permOK 4060 12 (mask 12) (4060 * 12) P PI = true)
    (hs : siftP P = true) : ruInPA (unpack 4060 12 P) :=
  ⟨RuLines.isInv_of rfl hp, siftK_sound bindsJ permJ RuJS.hl rfl (range_of_permOK hp) hs⟩

theorem e0_eq : ruE0[0]! = unpack 4060 12 A0 := by
  have : ruE0[0]! = ruA0A := rfl
  rw [this, ruA0A, A0]
  exact RuLines.row4060 (by norm_num)

theorem hE0 : ruEndE 0 = permOfArr 4060 (unpack 4060 12 A0) := by rw [ruEndE, e0_eq]

theorem hE1 : ruEndE 1 = permOfArr 4060 (unpack 4060 12 R) := by rw [ruEndE, r_eq, R]

theorem pE0 : PRep 4060 12 A0 (ruEndE 0) := by rw [hE0]; exact (prep_of pFacts.1).1

theorem pE1 : PRep 4060 12 R (ruEndE 1) := by rw [hE1]; exact (prep_of pFacts.2.2.1).1

theorem eAt (p : Fin 4060) : Nat.beq (fv A0 (fv A0 p)) p = true ∧ Nat.beq (fv R (fv R p)) p = true ∧
    Nat.beq (fv A0 (fv R p)) (fv R (fv A0 p)) = true ∧ ne (fv A0 p) p = true ∧
    ne (fv R p) p = true ∧ ne (fv A0 (fv R p)) p = true := by
  have h := eOK
  unfold eK at h
  have := CFSG.KS.allN_spec h p p.2
  simpa only [CFSG.KS.bAnd_iff] using this

theorem e_facts : (∀ i < 2, ruEndE i * ruEndE i = 1) ∧ ruEndE 0 * ruEndE 1 = ruEndE 1 * ruEndE 0 ∧
    ∀ p, ruEndE 0 p ≠ p ∧ ruEndE 1 p ≠ p ∧ (ruEndE 0 * ruEndE 1) p ≠ p := by
  refine ⟨fun i hi => ?_, comm_of pE0 pE1 fun p => (eAt p).2.2.1, fun p =>
    ⟨fpf_of pE0 (fun p => (eAt p).2.2.2.1) p, fpf_of pE1 (fun p => (eAt p).2.2.2.2.1) p,
      fpf2_of pE0 pE1 (fun p => (eAt p).2.2.2.2.2) p⟩⟩
  interval_cases i
  · exact sq_of pE0 fun p => (eAt p).1
  · exact sq_of pE1 fun p => (eAt p).2.1

theorem bcAt (p : Fin 4060) : cB A0 A0 p = true ∧ cB A0 R p = true ∧ cB R A0 p = true ∧
    cB R R p = true := by
  have h := bcOK
  unfold bcK at h
  have := CFSG.KS.allN_spec h p p.2
  simpa only [CFSG.KS.bAnd_iff] using this

theorem bn_facts : (∃ p < 4060, ne (cC p) p = true) ∧ (∃ p < 4060, ne (cC p) (fv A0 p) = true) ∧
    (∃ p < 4060, ne (cC p) (fv R p) = true) ∧
    ∃ p < 4060, ne (cC p) (fv A0 (fv R p)) = true := by
  have h := bnOK
  unfold bnK at h
  simp only [CFSG.KS.bAnd_iff] at h
  exact ⟨anyN_spec h.1, anyN_spec h.2.1, anyN_spec h.2.2.1, anyN_spec h.2.2.2⟩

theorem xcAt {i : Nat} (hi : i < 8) (p : Fin 4060) :
    Nat.beq (fv (X i) (fv A0 p)) (fv A0 (fv (X i) p)) = true ∧
      Nat.beq (fv (X i) (fv R p)) (fv R (fv (X i) p)) = true := by
  have h := xcOK
  unfold xcK at h
  have := CFSG.KS.allN_spec (CFSG.KS.allN_spec h i hi) p p.2
  simpa only [CFSG.KS.bAnd_iff] using this

theorem trAt (p : Fin 4060) :
    (∀ j < 4, Nat.beq (fv (Y j) p) (cm (X (Nat.mul 2 j)) (X (Nat.add (Nat.mul 2 j) 1))
      (XI (Nat.mul 2 j)) (XI (Nat.add (Nat.mul 2 j) 1)) p) = true) ∧
    Nat.beq (fv (Y 4) p) (cm (Y 0) (Y 1) (YI 0) (YI 1) p) = true ∧
    Nat.beq (fv (Y 5) p) (cm (Y 2) (Y 3) (YI 2) (YI 3) p) = true ∧
    Nat.beq (cm (Y 4) (Y 5) (YI 4) (YI 5) p) (fv A0 (cC p)) = true := by
  have h := trOK
  unfold trK at h
  have := CFSG.KS.allN_spec h p p.2
  simp only [CFSG.KS.bAnd_iff] at this
  exact ⟨CFSG.KS.allN_spec this.1, this.2⟩

@[expose] noncomputable def xP (i : Nat) : Equiv.Perm (Fin 4060) := permOfArr 4060 (unpack 4060 12 (X i))

@[expose] noncomputable def yP (i : Nat) : Equiv.Perm (Fin 4060) := permOfArr 4060 (unpack 4060 12 (Y i))

@[expose] noncomputable def bP : Equiv.Perm (Fin 4060) := permOfArr 4060 (unpack 4060 12 B)

theorem pX {i : Nat} (hi : i < 8) : PRep 4060 12 (X i) (xP i) ∧ PRep 4060 12 (XI i) (xP i)⁻¹ :=
  prep_of (pFacts.2.2.2.1 i hi)

theorem pY {i : Nat} (hi : i < 6) : PRep 4060 12 (Y i) (yP i) ∧ PRep 4060 12 (YI i) (yP i)⁻¹ :=
  prep_of (pFacts.2.2.2.2 i hi)

theorem pB : PRep 4060 12 B bP ∧ PRep 4060 12 BI bP⁻¹ := prep_of pFacts.2.1

theorem y_eq {j : Nat} (hj : j < 4) : yP j = ⁅xP (2 * j), xP (2 * j + 1)⁆ :=
  comm_eq (pX (i := 2 * j) (by omega)).1 (pX (i := 2 * j) (by omega)).2
    (pX (i := 2 * j + 1) (by omega)).1 (pX (i := 2 * j + 1) (by omega)).2 (pY (by omega)).1
    fun p => (trAt p).1 j hj

theorem tree_eq : tree3 (fun i : Fin 8 => xP i) = ruEndE 0 * (bP⁻¹ * ruEndE 0 * bP) := by
  have h4 : yP 4 = ⁅yP 0, yP 1⁆ := comm_eq (pY (by norm_num)).1 (pY (by norm_num)).2
    (pY (by norm_num)).1 (pY (by norm_num)).2 (pY (by norm_num)).1 fun p => (trAt p).2.1
  have h5 : yP 5 = ⁅yP 2, yP 3⁆ := comm_eq (pY (by norm_num)).1 (pY (by norm_num)).2
    (pY (by norm_num)).1 (pY (by norm_num)).2 (pY (by norm_num)).1 fun p => (trAt p).2.2.1
  have ht : ⁅yP 4, yP 5⁆ = ruEndE 0 * (bP⁻¹ * ruEndE 0 * bP) :=
    top_eq (pY (by norm_num)).1 (pY (by norm_num)).2 (pY (by norm_num)).1 (pY (by norm_num)).2
      pB.1 pB.2 pE0 fun p => (trAt p).2.2.2
  have y0 : yP 0 = ⁅xP 0, xP 1⁆ := y_eq (j := 0) (by norm_num)
  have y1 : yP 1 = ⁅xP 2, xP 3⁆ := y_eq (j := 1) (by norm_num)
  have y2 : yP 2 = ⁅xP 4, xP 5⁆ := y_eq (j := 2) (by norm_num)
  have y3 : yP 3 = ⁅xP 6, xP 7⁆ := y_eq (j := 3) (by norm_num)
  rw [tree3]
  change ⁅⁅⁅xP 0, xP 1⁆, ⁅xP 2, xP 3⁆⁆, ⁅⁅xP 4, xP 5⁆, ⁅xP 6, xP 7⁆⁆⁆ = _
  rw [← y0, ← y1, ← y2, ← y3, ← h4, ← h5, ht]

theorem conj_facts : ∃ b : Array ℕ, ∃ x : Fin 8 → Array ℕ, ruInPA b ∧ (∀ i, ruInPA (x i)) ∧
    (∀ i < 2, ∀ j < 2, ruEndE i * ((permOfArr 4060 b)⁻¹ * ruEndE j * permOfArr 4060 b) =
      (permOfArr 4060 b)⁻¹ * ruEndE j * permOfArr 4060 b * ruEndE i) ∧
    (permOfArr 4060 b)⁻¹ * ruEndE 0 * permOfArr 4060 b ∉
      ({1, ruEndE 0, ruEndE 1, ruEndE 0 * ruEndE 1} : Set (Equiv.Perm (Fin 4060))) ∧
    (∀ i, ∀ j < 2, permOfArr 4060 (x i) * ruEndE j = ruEndE j * permOfArr 4060 (x i)) ∧
    tree3 (fun i => permOfArr 4060 (x i)) =
      ruEndE 0 * ((permOfArr 4060 b)⁻¹ * ruEndE 0 * permOfArr 4060 b) := by
  obtain ⟨⟨p1, hp1, n1⟩, ⟨p2, hp2, n2⟩, ⟨p3, hp3, n3⟩, ⟨p4, hp4, n4⟩⟩ := bn_facts
  refine ⟨unpack 4060 12 B, fun i => unpack 4060 12 (X i.val), inPA_of pFacts.2.1 sB,
    fun i => inPA_of (pFacts.2.2.2.1 i i.2) (RuEndSX.all i i.2), fun i hi j hj => ?_, ?_,
    fun i j hj => ?_, tree_eq⟩
  · change ruEndE i * (bP⁻¹ * ruEndE j * bP) = bP⁻¹ * ruEndE j * bP * ruEndE i
    interval_cases i <;> interval_cases j
    · exact conjComm_of pB.1 pB.2 pE0 pE0 fun p => (bcAt p).1
    · exact conjComm_of pB.1 pB.2 pE0 pE1 fun p => (bcAt p).2.1
    · exact conjComm_of pB.1 pB.2 pE1 pE0 fun p => (bcAt p).2.2.1
    · exact conjComm_of pB.1 pB.2 pE1 pE1 fun p => (bcAt p).2.2.2
  · change bP⁻¹ * ruEndE 0 * bP ∉ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨conjNe_of pB.1 pB.2 pE0 (F := fun p => p) (fun p => rfl) ⟨p1, hp1, n1⟩,
      conjNe_of pB.1 pB.2 pE0 (ap pE0) ⟨p2, hp2, n2⟩,
      conjNe_of pB.1 pB.2 pE0 (ap pE1) ⟨p3, hp3, n3⟩,
      conjNe_of pB.1 pB.2 pE0 (F := fun p => fv A0 (fv R p))
        (fun p => by rw [Equiv.Perm.mul_apply, ap pE0, ap pE1]) ⟨p4, hp4, n4⟩⟩
  · change xP i * ruEndE j = ruEndE j * xP i
    interval_cases j
    · exact comm_of (pX i.2).1 pE0 fun p => (xcAt i.2 p).1
    · exact comm_of (pX i.2).1 pE1 fun p => (xcAt i.2 p).2

theorem sig_eq : ∀ i < 3, ∀ a < 5, sigK i a = ruEndSig i a := by decide

@[expose] noncomputable def gensS : List (Equiv.Perm (Fin 4060)) :=
  (List.range 5).map fun j => permOfArr 4060 (unpack 4060 12 (RuES.S j))

@[expose] noncomputable def arrS : Array (Array ℕ) := Array.ofFn (n := 5) fun j =>
  unpack 4060 12 (RuES.S j.val)

theorem pS {j : Nat} (hj : j < 5) :
    permOK 4060 12 (mask 12) (4060 * 12) (RuES.S j) (RuES.SI j) = true :=
  CFSG.KS.allN_spec (head_facts RuES.head).1 j hj

theorem nsOK : 4060 ≤ RuES.NS * 4 := Nat.le_of_ble_eq_true (by quickRfl)

theorem chainS : ChainK 4060 12 gensS noDerivs (#v[0] : Vector (Fin 4060) 1) RuES.S RuES.SI RuES.LR
    RuES.TR RuES.TRI 5 RuES.BP RuES.NS 4 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, RuES.head, RuES.hl,
    nsOK, RuES.hs⟩
  have hj5 : j < 5 := by simpa [gensS] using hj
  rw [List.getD_eq_getElem _ _ hj]
  simp only [gensS, List.getElem_map, List.getElem_range]
  exact imageList_of_rep (by simp [unpack]) (rep_permOfArr (isInvA_unpack (pS hj5))).1

theorem hbsS : (#v[0] : Vector (Fin 4060) 1).toList.Nodup := by decide

theorem arrS_get {k : Nat} (hk : k < 5) : arrS[k]! = unpack 4060 12 (RuES.S k) := by
  rw [arrS, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem permsA_arrS : permsA 4060 arrS = {g | g ∈ gensS} := by
  ext g
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, gensS, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk5 : k < 5 := by simpa [arrS] using hk
    exact ⟨k, hk5, by rw [arrS_get hk5]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by simpa [arrS] using hk, by rw [arrS_get hk]⟩

theorem closure_arrS : Subgroup.closure (permsA 4060 arrS) =
    (certificate (by norm_num) gensS noDerivs (#v[0] : Vector (Fin 4060) 1) hbsS).originalSubgroup := by
  rw [certificate_originalSubgroup, permsA_arrS]

theorem ordS : ordK RuES.LR 1 = 256 := by
  have e : ordK RuES.LR 1 = rcnt (RuES.LR 0) * 1 := rfl
  rw [e, beq_eq cntK]

theorem sylow_facts (hel : ∀ j < 256, elemOK j = true) : ∃ lab : Fin 4060 → ℕ, (∀ p, lab p < 5) ∧
    (∀ i < 3, ∀ p, lab (ruLStrong i p) = ruEndSig i (lab p)) ∧
    ∃ s : Array (Array ℕ), (∀ k < s.size, ruInPA s[k]! ∧
      permOfArr 4060 s[k]! * ruEndE 0 = ruEndE 0 * permOfArr 4060 s[k]!) ∧
      Nat.card (Subgroup.closure (permsA 4060 s)) = 256 ∧
      ∀ z ∈ Subgroup.closure (permsA 4060 s), z ^ 2 = 1 → (∀ p, lab (z p) = lab p) →
        ∃ p, z p = p := by
  have hlt : ∀ p : Fin 4060, fv LAB p < 5 := fun p => by
    have h := lOK
    unfold lK at h
    exact Nat.blt_eq.mp (CFSG.KS.allN_spec h p p.2)
  refine ⟨fun p => fv LAB p, hlt, fun i hi p => ?_, arrS, fun k hk => ?_, ?_, ?_⟩
  · have hk : 39 + i < 45 := by omega
    have hl : ruLStrong i = permOfArr 4060 (unpack 4060 12 (RuT4060.L (Nat.add 39 i))) := by
      rw [ruLStrong, field_get5 (by omega), RuLines.row4060 hk]
      rfl
    have hp : PRep 4060 12 (RuT4060.L (Nat.add 39 i)) (ruLStrong i) := by
      rw [hl]
      exact (prep_of (CFSG.KS.allN_spec pL i hi)).1
    have h := lsOK
    unfold lsK at h
    change fv LAB ((ruLStrong i p : Fin 4060) : ℕ) = ruEndSig i (fv LAB p)
    rw [lab_of hp (fun p => CFSG.KS.allN_spec (CFSG.KS.allN_spec h i hi) p p.2) p,
      sig_eq i hi _ (hlt p)]
  · have hk5 : k < 5 := by simpa [arrS] using hk
    rw [arrS_get hk5]
    refine ⟨inPA_of (pS hk5) (RuEndSS.all k hk5), ?_⟩
    have h := scOK
    unfold scK at h
    exact comm_of (prep_of (pS hk5)).1 pE0 fun p =>
      CFSG.KS.allN_spec (CFSG.KS.allN_spec h k hk5) p p.2
  · rw [closure_arrS, card_group chainS (by norm_num) hbsS, ordS]
  · intro z hz hz2 hlab
    rw [closure_arrS] at hz
    obtain ⟨j, hj, rfl⟩ := (mem_group_iff chainS (by norm_num) hbsS z).1 hz
    rw [ordS] at hj
    have h := hel j hj
    unfold elemOK at h
    rw [CFSG.KS.Raw.Orb.strictB_eq] at h
    exact fix_of (prep_elemK chainS j) h hz2 hlab

theorem ruEndFactsK_of (hel : ∀ j < 256, elemOK j = true) : RuEndFactsK := by
  obtain ⟨h1, h2, h3⟩ := e_facts
  refine ⟨fun i hi => ?_, h1, h2, h3, conj_facts, sylow_facts hel⟩
  interval_cases i
  · rw [e0_eq]
    exact inPA_of pFacts.1 sA0
  · rw [r_eq]
    exact inPA_of pFacts.2.2.1 sR

end CertificateChecks.KernelSporSch.RuEnd

end
