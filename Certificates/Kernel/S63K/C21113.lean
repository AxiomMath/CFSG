module

public import CFSG.LargeExtraspecial.S63CD4Inputs
public import Certificates.Kernel.S63K.CChecks
import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelS63.C21113

open CFSG.LargeExtraspecial.S63 CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.KS.SporSch.M24 CFSG.KC.Enum
  CFSG.KS CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CertificateChecks.KernelS63.CD

theorem cg_size : cGens.size = 4 := by decide +kernel

theorem cg_eq : ∀ l < 4, cGens[l]! = unpackR 24 (CG l) := by
  intro l hl
  interval_cases l <;> decide +kernel

theorem t0_eq : t0R = unpackR 24 (T0 0) := by decide +kernel

@[expose] def resIP (r : Option (Array ℕ) × Array ℕ × Array ℕ) : Array ℕ :=
  match r.1 with
  | some a => a
  | none => r.2.2

@[expose] def bodyIP (x : Array ℕ) (_ : ℕ) (r : Option (Array ℕ) × Array ℕ × Array ℕ) :
    Id (ForInStep (Option (Array ℕ) × Array ℕ × Array ℕ)) :=
  if (r.2.1 == oneR) = true then pure (ForInStep.done (some r.2.2, r.2.1, r.2.2))
  else pure (ForInStep.yield (none, mulR r.2.1 x, r.2.1))

theorem loopIP (X : ℕ) : ∀ n s (p q : ℕ),
    resIP (forIn (m := Id) (List.range' s n) ((none : Option (Array ℕ)), unpackR 24 p,
      unpackR 24 q) (bodyIP (unpackR 24 X))) = unpackR 24 (ipK X n p q) := by
  intro n
  induction n with
  | zero => intro s p q; rfl
  | succ n ih =>
    intro s p q
    rw [List.range'_succ, List.forIn_cons]
    unfold bodyIP
    rw [oneR_eq, beq_unpackR, Nat.mod_eq_of_lt idP_lt]
    by_cases hp : p % 2 ^ 576 = idP
    · have hb : Nat.beq (p % 2 ^ 576) idP = true := by rw [hp]; exact Nat.beq_refl _
      simp only [hb, ↓reduceIte]
      unfold ipK
      rw [if_pos hp]
      rfl
    · have hb : Nat.beq (p % 2 ^ 576) idP = false := by
        cases e : Nat.beq (p % 2 ^ 576) idP
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hp
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      unfold ipK
      rw [if_neg hp, mulR_unpackR, ← oneR_eq]
      exact ih (s + 1) _ p

theorem invPow_eq (x : Array ℕ) : invPow x =
    resIP (forIn (m := Id) (List.range' 0 64) ((none : Option (Array ℕ)), x, oneR) (bodyIP x)) := by
  have e : ∀ (init : Option (Array ℕ) × Array ℕ × Array ℕ)
      (f : ℕ → Option (Array ℕ) × Array ℕ × Array ℕ →
        Id (ForInStep (Option (Array ℕ) × Array ℕ × Array ℕ))),
      forIn (m := Id) [:64] init f = forIn (m := Id) (List.range' 0 64) init f := by
    intro init f
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  unfold invPow
  dsimp only
  rw [e]
  generalize hR : forIn (m := Id) (List.range' 0 64) ((none : Option (Array ℕ)), x, oneR) _ = R
  have h2 : forIn (m := Id) (List.range' 0 64) ((none : Option (Array ℕ)), x, oneR) (bodyIP x) = R :=
    hR
  rw [h2]
  rcases R with ⟨_ | r, a, b⟩ <;> rfl

theorem invPow_unpackR (X : ℕ) : invPow (unpackR 24 X) = unpackR 24 (ipK X 64 X idP) := by
  have h := loopIP X 64 0 X idP
  rw [← oneR_eq] at h
  exact (invPow_eq _).trans h

@[expose] noncomputable def El : Array (Array ℕ) := Array.ofFn (n := 3072) fun i => unpackR 24 (EP i.val)

@[expose] noncomputable def Dk : EnumData :=
  { El := El, P := Array.ofFn (n := 3072) (fun i => EPar i.val),
    K := Array.ofFn (n := 3072) (fun i => ELab i.val), idx := lookup (mkIdx El),
    inv := El.map fun x => lookup (mkIdx El) (invPow x) }

theorem facts : enumBFS cGens = (El, Array.ofFn (n := 3072) (fun i => EPar i.val),
      Array.ofFn (n := 3072) (fun i => ELab i.val)) ∧ ETree CG EP EPar ELab 4 3072 ∧
    (∀ i < 3072, EP i < 2 ^ 576) ∧ ∀ a < 3072, ∀ b < 3072, EP a = EP b → a = b :=
  enumBFS_of_K (W := EW) (S := ES) cg_size cg_eq CertificateChecks.KernelS63.CD.rep

theorem mkEnum_eq : mkEnum cGens = Dk := by
  unfold mkEnum
  rw [facts.1]
  rfl

theorem el_get {i : ℕ} (hi : i < 3072) : El[i]! = unpackR 24 (EP i) := by
  rw [getElem!_pos El i (by simp [El, hi])]
  simp [El]

theorem idx_get {w : ℕ} (hw : w < 3072) : lookup (mkIdx El) (unpackR 24 (EP w)) = w :=
  lookup_mkIdx facts.2.2.1 facts.2.2.2 hw

theorem invK_get {i : ℕ} (hi : i < 3072) : EInv i < 3072 ∧
    EP (EInv i) = ipK (EP i) 64 (EP i) idP % 2 ^ 576 ∧ eqP (mw (EP i) (EP (EInv i))) idP = true := by
  have h := MatL.allN_iff.1 CertificateChecks.KernelS63.CD.inv i hi
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2⟩

theorem inv_get {i : ℕ} (hi : i < 3072) : Dk.inv[i]! = EInv i := by
  have hsz : Dk.inv.size = 3072 := by simp [Dk, El]
  rw [getElem!_pos Dk.inv i (by rw [hsz]; exact hi)]
  simp only [Dk, Array.getElem_map]
  rw [← getElem!_pos El i (by simp [El, hi]), el_get hi, invPow_unpackR, unpackR_mod,
    ← (invK_get hi).2.1, idx_get (invK_get hi).1]

theorem clos_get {h l : ℕ} (hh : h < 3072) (hl : l < 4) :
    EW (h * 4 + l) < 3072 ∧ EP (EW (h * 4 + l)) = stepK CG (EP h) l := by
  have h1 := MatL.allN_iff.1 (MatL.allN_iff.1 CertificateChecks.KernelS63.CD.clos h hh) l hl
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h1
  exact ⟨h1.1, Nat.eq_of_beq_eq_true h1.2⟩

theorem mul_get {l i : ℕ} (hl : l < 4) (hi : i < 3072) :
    mulR cGens[l]! El[i]! = unpackR 24 (stepK CG (EP i) l) := by
  rw [el_get hi]
  exact step_eq cg_eq _ hl

theorem find_congr {p q : ℕ → Bool} : ∀ {l : List ℕ}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      find_congr fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem all_congr {p q : ℕ → Bool} : ∀ {l : List ℕ}, (∀ x ∈ l, p x = q x) → l.all p = l.all q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      all_congr fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem any_congr {p q : ℕ → Bool} : ∀ {l : List ℕ}, (∀ x ∈ l, p x = q x) → l.any p = l.any q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      any_congr fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem c3_eq : findOrder3 Dk = C3 0 := by
  unfold findOrder3
  have hsz : Dk.El.size = 3072 := by simp [Dk, El]
  rw [hsz]
  have e : (List.range 3072).find? (fun i => !Dk.El[i]! == oneR &&
      mulR (mulR Dk.El[i]! Dk.El[i]!) Dk.El[i]! == oneR) = (List.range 3072).find? o3K := by
    apply find_congr
    intro i hi
    have hi' := List.mem_range.1 hi
    change (!El[i]! == oneR && mulR (mulR El[i]! El[i]!) El[i]! == oneR) = _
    rw [el_get hi', oneR_eq, mulR_unpackR, mulR_unpackR, beq_unpackR, beq_unpackR]
    rfl
  rw [e, CertificateChecks.KernelS63.CD.c3]
  rfl

theorem sq12_eq : ∀ (l : List ℕ) (X : ℕ),
    l.foldl (fun acc _ => mulR acc acc) (unpackR 24 X) =
      unpackR 24 (l.foldl (fun acc _ => mw acc acc) X)
  | [], _ => rfl
  | a :: l, X => by
    rw [List.foldl_cons, List.foldl_cons, mulR_unpackR]
    exact sq12_eq l _

theorem inv3_lt : EInv (C3 0) < 3072 := (invK_get c3lt).1

theorem p2_eq : twoSet Dk (C3 0) = P2L := by
  unfold twoSet P2L
  apply List.filter_congr
  intro i hi
  have hi' := List.mem_range.1 hi
  change (sq12R El[i]! == oneR && sq12R (mulR El[i]! (conjI El[C3 0]! El[Dk.inv[C3 0]!]! El[i]!))
    == oneR) = _
  rw [inv_get c3lt, el_get hi', el_get c3lt, el_get inv3_lt]
  unfold sq12R conjI
  rw [mulR_unpackR, mulR_unpackR, mulR_unpackR, sq12_eq, sq12_eq, oneR_eq, beq_unpackR,
    beq_unpackR]
  rfl

theorem p2_lt {i : ℕ} (hi : i ∈ P2L) : i < 3072 := by
  unfold P2L at hi
  exact List.mem_range.1 (List.mem_of_mem_filter hi)

theorem z_eq : zSet Dk P2L = ZL := by
  unfold zSet ZL
  apply List.filter_congr
  intro i hi
  apply all_congr
  intro j hj
  change (mulR El[i]! El[j]! == mulR El[j]! El[i]!) = _
  rw [el_get (p2_lt hi), el_get (p2_lt hj), mulR_unpackR, mulR_unpackR, beq_unpackR]
  rfl

theorem z_lt {j : ℕ} (hj : j ∈ ZL) : j < 3072 := by
  unfold ZL at hj
  exact p2_lt (List.mem_of_mem_filter hj)

theorem ok_eq : Dk.ok cGens 3072 = true := by
  unfold EnumData.ok enumOK
  have hsz : Dk.El.size = 3072 := by simp [Dk, El]
  have hroot : EP 0 = idP := (bfsK_sound rep).2.1
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hsz]
  refine ⟨⟨⟨by norm_num, ?_⟩, ?_⟩, trivial⟩
  · change El[0]! = oneR
    rw [el_get (by norm_num), hroot, oneR_eq]
  · refine allLt_iff.2 fun i hi => ?_
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    change ((validR El[i]! = true ∧ lookup (mkIdx El) El[i]! = i) ∧ (i = 0 ∨
      ((Dk.P[i]! < i ∧ Dk.K[i]! < cGens.size) ∧ El[i]! = mulR cGens[Dk.K[i]!]! El[Dk.P[i]!]!))) ∧
      allLt cGens.size (fun k => decide (lookup (mkIdx El) (mulR cGens[k]! El[i]!) < 3072) &&
        El[lookup (mkIdx El) (mulR cGens[k]! El[i]!)]! == mulR cGens[k]! El[i]!) = true
    rw [el_get hi, validR_unpackR, idx_get hi, cg_size]
    refine ⟨⟨⟨rfl, rfl⟩, ?_⟩, ?_⟩
    · by_cases h0 : i = 0
      · exact Or.inl h0
      · right
        have ht := facts.2.1
        unfold ETree at ht
        obtain ⟨h1, h2, h3⟩ := ht i (by omega) hi
        have ep : Dk.P[i]! = EPar i := by simp [Dk, getElem!_pos, hi]
        have ek : Dk.K[i]! = ELab i := by simp [Dk, getElem!_pos, hi]
        rw [ep, ek, mul_get h2 (by omega), ← h3]
        exact ⟨⟨h1, h2⟩, rfl⟩
    · refine allLt_iff.2 fun k hk => ?_
      obtain ⟨hw, hpw⟩ := clos_get hi hk
      rw [step_eq cg_eq _ hk, ← hpw, idx_get hw, el_get hw]
      simp [hw]

theorem invOK_eq : Dk.invOK 3072 = true := by
  unfold EnumData.invOK
  refine allLt_iff.2 fun i hi => ?_
  obtain ⟨h1, -, h3⟩ := invK_get hi
  change (decide (Dk.inv[i]! < 3072) && mulR El[i]! El[Dk.inv[i]!]! == oneR) = true
  rw [inv_get hi, el_get hi, el_get h1, mulR_unpackR, oneR_eq, beq_unpackR]
  simp only [h1, decide_true, Bool.true_and]
  exact h3

theorem gens_ok : gensOK cGens = true := by
  unfold gensOK
  rw [cg_size]
  refine allLt_iff.2 fun k hk => ?_
  rw [cg_eq k hk, mulR_unpackR, oneR_eq, beq_unpackR]
  interval_cases k <;> decide +kernel

theorem comm_ok : (allLt cGens.size fun k => mulR cGens[k]! t0R == mulR t0R cGens[k]!) = true := by
  rw [cg_size]
  refine allLt_iff.2 fun k hk => ?_
  rw [cg_eq k hk, t0_eq, mulR_unpackR, mulR_unpackR, beq_unpackR]
  interval_cases k <;> decide +kernel

theorem cm_pt {i c : ℕ} (hi : i < 3072) (hc : c < 3072) :
    commI Dk.El[i]! Dk.El[Dk.inv[i]!]! Dk.El[c]! Dk.El[Dk.inv[c]!]! = unpackR 24 (cmK i c) := by
  change commI El[i]! El[Dk.inv[i]!]! El[c]! El[Dk.inv[c]!]! = _
  rw [inv_get hi, inv_get hc, el_get hi, el_get hc, el_get (invK_get hi).1,
    el_get (invK_get hc).1]
  unfold commI
  rw [mulR_unpackR, mulR_unpackR, mulR_unpackR]
  rfl

theorem fin_pt {i : ℕ} (hi : i ∈ P2L) :
    (ZL.contains i || (List.range 3072).any fun c =>
      ZL.any (fun j => Dk.El[j]! == commI Dk.El[i]! Dk.El[Dk.inv[i]!]! Dk.El[c]! Dk.El[Dk.inv[c]!]!) &&
        !(commI Dk.El[i]! Dk.El[Dk.inv[i]!]! Dk.El[c]! Dk.El[Dk.inv[c]!]! == oneR) &&
        !(commI Dk.El[i]! Dk.El[Dk.inv[i]!]! Dk.El[c]! Dk.El[Dk.inv[c]!]! == t0R)) = finK i := by
  unfold finK
  have hi' := p2_lt hi
  have e : ((List.range 3072).any fun c =>
      ZL.any (fun j => Dk.El[j]! == commI Dk.El[i]! Dk.El[Dk.inv[i]!]! Dk.El[c]! Dk.El[Dk.inv[c]!]!) &&
        !(commI Dk.El[i]! Dk.El[Dk.inv[i]!]! Dk.El[c]! Dk.El[Dk.inv[c]!]! == oneR) &&
        !(commI Dk.El[i]! Dk.El[Dk.inv[i]!]! Dk.El[c]! Dk.El[Dk.inv[c]!]! == t0R)) =
      ((List.range 3072).any fun c =>
        ZL.any (fun j => eqP (EP j) (cmK i c)) && !eqP (cmK i c) idP && !eqP (cmK i c) (T0 0)) := by
    apply any_congr
    intro c hc
    have hc' := List.mem_range.1 hc
    rw [cm_pt hi' hc', oneR_eq, t0_eq, beq_unpackR, beq_unpackR]
    have ez : ZL.any (fun j => Dk.El[j]! == unpackR 24 (cmK i c)) =
        ZL.any (fun j => eqP (EP j) (cmK i c)) := by
      apply any_congr
      intro j hj
      change (El[j]! == _) = _
      rw [el_get (z_lt hj), beq_unpackR]
      rfl
    rw [ez]
    rfl
  rw [e]

open CFSG.LargeExtraspecial.S63 in
theorem c21113 : d4BCheck = true := by
  unfold d4BCheck
  rw [mkEnum_eq]
  simp only []
  rw [c3_eq, p2_eq, z_eq]
  unfold d4BCheckOn
  simp only [gens_ok, comm_ok, ok_eq, invOK_eq, c3lt, zlen, decide_true, Bool.true_and,
    Bool.and_true]
  refine (all_congr fun i hi => ?_).trans CertificateChecks.KernelS63.CD.fin
  exact fin_pt hi

end CertificateChecks.KernelS63.C21113

end
