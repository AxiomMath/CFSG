module

public import Certificates.Kernel.TwoHSLe4.NormQ
public import Certificates.Kernel.TwoHSLe4.NormPSound

public section

namespace CertificateChecks.KernelTwoHSLe4.NormP

open CFSG.EvenSporadicStandard.TwoHS CFSG.KC.F4M3B CFSG.KC.Enum
  CertificateChecks.KernelTwoHSLe4.Norm

variable {α β : Type}

theorem chkA_eq (o : Ops α) (hbd : ∀ y k, o.bd y k = k y) (L N : List R4) (h : ℕ → α) :
    chkA o L N h = finA o N (inA o h) (L.map fun s => mulM o (inA o h) (cQ o s))
      (L.map fun s => mulM o (cQ o s) (inA o h)) := by
  simp only [chkA, bindQ_eq o hbd, bindL_eq o hbd]

section map

variable (o : Ops α) (o' : Ops β) (f : α → β) (ha : ∀ p q, f (o.a p q) = o'.a (f p) (f q))
  (hx : ∀ p q, f (o.x p q) = o'.x (f p) (f q)) (ht : f o.t = o'.t)
include ha hx ht

theorem inA_map (h : ℕ → α) : (inA o h).map f = inA o' (fun j => f (h j)) := by
  simp only [inA, Q4.map, pm, zr_map o o' f ha hx ht]

theorem eqL_map (A B : Q4 α) : f (eqL o A B) = eqL o' (A.map f) (B.map f) := by
  simp only [eqL, eqLE, Q4.map, pm, ha, hx, bnot_map' o o' f ha hx ht]

theorem finA_map (N : List R4) (A : Q4 α) (P Q : List (Q4 α)) :
    f (finA o N A P Q) = finA o' N (A.map f) (P.map (Q4.map f)) (Q.map (Q4.map f)) := by
  simp only [finA, bor_map' o o' f ha hx ht, bnot_map' o o' f ha hx ht, ha,
    allA_map o o' f ha hx ht, anyA_map o o' f ha hx ht, List.map_map, Function.comp_def,
    eqL_map o o' f ha hx ht, eqM_map o o' f ha hx ht, cQ_map o o' f ha hx ht]

end map

theorem eqLb (r s : ℕ) :
    bnot boolOps (boolOps.x (Nat.beq (r % 2) 1) (Nat.beq (s % 2) 1)) = (r % 2 == s % 2) := by
  rcases Nat.mod_two_eq_zero_or_one r with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one s with g | g <;> rw [h, g] <;> rfl

theorem eqL_enc (x y : R4) : eqL boolOps (encQ x) (encQ y) = (x.mod2 == y.mod2) := by
  simp only [eqL, eqLE, encQ, enc, eqLb, a_bool]
  rw [Bool.eq_iff_iff]
  cases x
  cases y
  simp only [R4.mod2, Bool.and_eq_true, beq_iff_eq, R4.mk.injEq]

theorem finA_enc (N : List R4) (hN : ∀ c ∈ N, c.wf) (L : List R4) {a : R4} (ha : a.wf) :
    finA boolOps N (encQ a) (L.map fun s => encQ (rmul a s)) (L.map fun s => encQ (rmul s a)) =
      (!((L.all fun s => L.any fun s' => (rmul a s).mod2 == (rmul s' a).mod2) &&
        (L.all fun s' => L.any fun s => (rmul a s).mod2 == (rmul s' a).mod2)) ||
        N.any fun c => a == c) := by
  have hc : (N.map fun c => eqM boolOps (encQ a) (cQ boolOps c)) = N.map fun c => a == c := by
    refine List.map_congr_left fun c hc => ?_
    rw [cQ_enc, eqM_enc ha (hN c hc)]
  simp only [finA, hc, allA_bool, anyA_bool, List.map_map, Function.comp_def, bor_bool,
    bnot_bool, a_bool, List.all_map, List.any_map, id, eqL_enc]

theorem ent_bit (y : ℕ) : (decide (y % 2 = 1), zr boolOps) = enc (y % 2) := by
  unfold enc
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;> rw [h] <;> rfl

theorem inA_bits (n : ℕ) : inA boolOps (fun j => n.testBit j) = encQ (bitsOf n) := by
  simp only [inA, Nat.testBit_eq_decide_div_mod_eq, pow_zero, Nat.div_one, Nat.reducePow,
    encQ, bitsOf]
  simp only [ent_bit]

theorem wf_rowR (P : ℕ) : (rowR P).wf := by
  have g : ∀ i < 16, ((List.range 16).map (pg 2 3 P)).getD i 0 = pg 2 3 P i := by
    intro i hi
    simp [List.getD_eq_getElem?_getD, hi]
  have h : ∀ i, pg 2 3 P i < 4 := fun i => by
    unfold pg
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
  simp only [rowR, R4.ofList, R4.wf, g 0 (by omega), g 1 (by omega), g 2 (by omega),
    g 3 (by omega), g 4 (by omega), g 5 (by omega), g 6 (by omega), g 7 (by omega),
    g 8 (by omega), g 9 (by omega), g 10 (by omega), g 11 (by omega), g 12 (by omega),
    g 13 (by omega), g 14 (by omega), g 15 (by omega)]
  exact ⟨h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _⟩

theorem wf_nvL : ∀ c ∈ nvL, c.wf := by
  intro c hc
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact wf_rowR _

theorem fin_of_chkAG {L N : List R4} (h : chkAG L N = true) {n : ℕ} (hn : n < 2 ^ 16) :
    finA boolOps N (encQ (bitsOf n)) (L.map fun s => encQ (rmul (bitsOf n) s))
      (L.map fun s => encQ (rmul s (bitsOf n))) = true := by
  unfold chkAG at h
  simp only [frcL_eq, frc_eq] at h
  generalize hT : Nat.sub (Nat.pow 2 (Nat.pow 2 16)) 1 = T at h
  have hTn : tbit n T = true := by
    rw [← hT]
    exact ones_bit (Nat.pow 2 16) n hn
  have ha : ∀ p q, tbit n ((natOps T).a p q) = boolOps.a (tbit n p) (tbit n q) :=
    fun p q => Nat.testBit_and p q n
  have hx : ∀ p q, tbit n ((natOps T).x p q) = boolOps.x (tbit n p) (tbit n q) :=
    fun p q => Nat.testBit_xor p q n
  have e := congrArg (tbit n) (Nat.eq_of_beq_eq_true h)
  rw [hTn, chkA_eq _ (fun y k => frcN_eq y k),
    finA_map (natOps T) boolOps (tbit n) ha hx hTn] at e
  have hA : (inA (natOps T) fun j => pln j 16).map (tbit n) = encQ (bitsOf n) := by
    rw [inA_map (natOps T) boolOps (tbit n) ha hx hTn]
    simp only [tbit, pln_bit, hn, decide_true, Bool.true_and]
    exact inA_bits n
  simp only [List.map_map, Function.comp_def, mulM_map (natOps T) boolOps (tbit n) ha hx,
    cQ_map (natOps T) boolOps (tbit n) ha hx hTn, hA, cQ_enc, mulM_enc] at e
  exact e

theorem mem_nvL_of_chkAN (h : chkAN = true) {b : R4} (hb : b.wf2) (hN : normB2S b = true) :
    b ∈ nvL := by
  have h' : chkAG (SL.map R4.mod2) nvL = true := h
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 (mem_bitsN hb)
  have hlt : n < 2 ^ 16 := List.mem_range.1 hn
  have hw : (bitsOf n).wf := by
    simp only [bitsOf, R4.wf]
    omega
  have e := fin_of_chkAG h' hlt
  rw [finA_enc nvL wf_nvL _ hw] at e
  have e' : (!normB2S (bitsOf n) || nvL.any fun c => bitsOf n == c) = true := e
  rw [hN, Bool.not_true, Bool.false_or, List.any_eq_true] at e'
  obtain ⟨c, hc, hbc⟩ := e'
  rw [beq_iff_eq] at hbc
  rw [hbc]
  exact hc

end CertificateChecks.KernelTwoHSLe4.NormP

end
