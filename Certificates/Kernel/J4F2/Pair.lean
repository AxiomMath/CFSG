module

public import Certificates.Kernel.J4Q.MaskRep
public import CFSG.Certificates.Kernel.J4Q.RepQT2B
public import Certificates.Data.CFSGNative.H13.J4Elems

public section

namespace CertificateChecks.KernelJ4F2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native
open CertificateChecks.KernelJ4Q

@[expose] def PE (p : Pr) (q : Nat × Nat) : Prop :=
  (WfA p.1 ∧ encR p.1 = q.1) ∧ (WfA p.2 ∧ encR p.2 = q.2)

@[expose] noncomputable def prOneK : Nat × Nat := (one, one)

@[expose] noncomputable def prMulK (x y : Nat × Nat) : Nat × Nat :=
  (mulJ c rm x.1 y.1, mulJ c rm y.2 x.2)

@[expose] noncomputable def prInvK (x : Nat × Nat) : Nat × Nat := (x.2, x.1)

@[expose] noncomputable def prLetterK (gs : List (Nat × Nat)) (l : Int) : Nat × Nat :=
  if 0 < l then gs.getD (l.toNat - 1) prOneK else prInvK (gs.getD ((-l).toNat - 1) prOneK)

@[expose] noncomputable def prWordK (gs : List (Nat × Nat)) (w : List Int) : Nat × Nat :=
  w.foldl (fun acc l => prMulK acc (prLetterK gs l)) prOneK

@[expose] noncomputable def prPowK (x : Nat × Nat) : Nat → Nat × Nat
  | 0 => prOneK
  | e + 1 => prMulK (prPowK x e) x

theorem pe_one : PE (prOne ()) prOneK := ⟨mkId, mkId⟩

theorem pe_mul {x y : Pr} {a b : Nat × Nat} (hx : PE x a) (hy : PE y b) :
    PE (prMul x y) (prMulK a b) :=
  ⟨mkMul hx.1 hy.1, mkMul hy.2 hx.2⟩

theorem pe_inv {x : Pr} {a : Nat × Nat} (hx : PE x a) : PE (prInv x) (prInvK a) := ⟨hx.2, hx.1⟩

theorem pe_pow {x : Pr} {a : Nat × Nat} (hx : PE x a) : ∀ e, PE (prPow x e) (prPowK a e)
  | 0 => pe_one
  | e + 1 => pe_mul (pe_pow hx e) hx

@[expose] def PT (gs : Array Pr) (gK : List (Nat × Nat)) : Prop :=
  ∀ k, PE (gs[k]?.getD (prOne ())) (gK.getD k prOneK)

theorem pe_letter {gs : Array Pr} {gK : List (Nat × Nat)} (h : PT gs gK) (l : Int) :
    PE (prLetter gs l) (prLetterK gK l) := by
  unfold prLetter prLetterK
  split
  · exact h _
  · exact pe_inv (h _)

theorem pe_fold {f : Nat → Pr} {fK : Nat → Nat × Nat} (h : ∀ i, PE (f i) (fK i)) :
    ∀ (l : List Nat) {acc : Pr} {a : Nat × Nat}, PE acc a →
      PE (l.foldl (fun acc i => prMul acc (f i)) acc) (l.foldl (fun acc i => prMulK acc (fK i)) a)
  | [], _, _, h0 => h0
  | i :: l, _, _, h0 => pe_fold h l (pe_mul h0 (h i))

theorem pe_foldW {gs : Array Pr} {gK : List (Nat × Nat)} (h : PT gs gK) :
    ∀ (w : List Int) {acc : Pr} {a : Nat × Nat}, PE acc a →
      PE (w.foldl (fun acc l => prMul acc (prLetter gs l)) acc)
        (w.foldl (fun acc l => prMulK acc (prLetterK gK l)) a)
  | [], _, _, h0 => h0
  | l :: w, _, _, h0 => pe_foldW h w (pe_mul h0 (pe_letter h l))

theorem pe_word {gs : Array Pr} {gK : List (Nat × Nat)} (h : PT gs gK) (w : List Int) :
    PE (prWord gs w) (prWordK gK w) :=
  pe_foldW h w pe_one

@[expose] noncomputable def baseK : List (Nat × Nat) := [(A, Ai), (B, Bi)]

theorem pt_base : PT (basePairs ()) baseK := by
  intro k
  rcases k with _ | _ | k
  · exact ⟨base_gens 0, base_invs 0⟩
  · exact ⟨base_gens 1, base_invs 1⟩
  · have e : (basePairs ())[k + 2]? = none := by simp [basePairs]
    rw [e]
    exact pe_one

theorem pt_ofList (f : Nat → Pr) (fK : Nat → Nat × Nat) (h : ∀ i, PE (f i) (fK i)) (n : Nat) :
    PT ((List.range n).toArray.map f) ((List.range n).map fK) := by
  intro k
  by_cases hk : k < n
  · simp only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hk, Option.map_some,
      Option.getD_some]
    rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    simpa using h k
  · have e1 : ((List.range n).toArray.map f)[k]? = none := by
      simp only [Array.getElem?_map, List.getElem?_toArray, Option.map_eq_none_iff,
        List.getElem?_eq_none_iff, List.length_range]
      omega
    have e2 : ((List.range n).map fK).getD k prOneK = prOneK :=
      List.getD_eq_default _ _ (by simp only [List.length_map, List.length_range]; omega)
    rw [e1, e2]
    exact pe_one

theorem rowsNe_of {X Y : Array V2} {x y : Nat} (hX : WfA X ∧ encR X = x) (hY : WfA Y ∧ encR Y = y)
    (h : neN x y = true) : rowsNe X Y = true := by
  rw [← hX.2, ← hY.2] at h
  have hne : encR X ≠ encR Y := fun e => by
    have hb := beq_false h
    rw [e, Nat.beq_refl] at hb
    exact Bool.noConfusion hb
  by_contra hr
  apply hne
  simp only [rowsNe, Bool.not_eq_true, List.any_eq_false, List.mem_range] at hr
  apply Nat.eq_of_testBit_eq
  intro p
  rw [encR_bit, encR_bit]
  by_cases hp : p / 128 < 112
  · have hv := hr (p / 128) hp
    simp only [vNe, Bool.not_eq_true, List.any_eq_false, List.mem_range, bne_iff_ne, ne_eq,
      Decidable.not_not] at hv
    have hm : p % 128 < 128 := Nat.mod_lt _ (by omega)
    by_cases hj : p % 128 < 112
    · rw [← testBit_v2N _ hm, ← testBit_v2N _ hm, hv _ hj]
    · have wX := CFSG.Sporadic.J4.rows_getD_wf (rows_wf_of hX.1) (p / 128)
      have wY := CFSG.Sporadic.J4.rows_getD_wf (rows_wf_of hY.1) (p / 128)
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (v2N_lt112 wX)
          (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (v2N_lt112 wY)
          (Nat.pow_le_pow_right (by omega) (by omega)))]
  · simp [hp]

end CertificateChecks.KernelJ4F2

end
