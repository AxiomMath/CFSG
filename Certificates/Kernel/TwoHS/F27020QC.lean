module

public import Certificates.Kernel.TwoHS.F27020Facts
public import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS
open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Recognition.HSMultiplier

@[expose] noncomputable def pc27C (p q : Nat) : Nat := pcompC 11200 14 (mask 14) p q

theorem pc27C_eq : pc27C = pc := by
  funext p q
  exact CFSG.KS.PK.pcompC_eq 11200 14 p q

@[expose] noncomputable def EVKC (G GI : Fin 6 → Nat) (wd : List (Fin 6 × Bool)) : Nat :=
  wd.foldl (fun acc l => pc27C acc (cond l.2 (G l.1) (GI l.1))) idK

@[expose] noncomputable def prodKC (E : Fin 4 → Nat) (m : Nat) : Nat :=
  (List.finRange 4).foldl (fun acc l => cond (m.testBit l.val) (pc27C acc (E l)) acc) idK

@[expose] noncomputable def ckBodyQC (I : Nat) (T A : Fin 6 → Nat) (E F : Fin 4 → Nat)
    (P : Fin 16 → Nat) : Bool :=
  bAnd((List.finRange 6).all (fun j => Nat.beq (pc27C (T j) (T j)) I),
  bAnd((List.finRange 6).all (fun k => Nat.beq (pc27C (A k) (A k)) I),
  bAnd((List.finRange 4).all (fun l => Nat.beq (E l) (F l)),
  bAnd((List.finRange 4).all (fun l => Nat.beq (pc27C (E l) (E l)) I),
  bAnd((List.finRange 4).all (fun l => (List.finRange 4).all fun l' =>
    (Nat.ble l'.val l.val || Nat.beq (pc27C (E l) (E l')) (pc27C (E l') (E l)))),
  dist16 P)))))

@[expose] noncomputable def ck27020QC (i : Fin 4) : Bool :=
  strictB idK fun I =>
  bind6 (fun j => EVKC HYF HYF (hfxW i j)) fun T =>
  bind6 (fun k => EVKC T T (hsCommWord k)) fun A =>
  bind4 (fun l => EVKC HYF HYF (hfxE i l)) fun E =>
  bind4 (fun l => EVKC A A (hfxE i l)) fun F =>
  bind16 (fun m => prodKC E m.val) fun P =>
  ckBodyQC I T A E F P

theorem ck27020QC_eq (i : Fin 4) : ck27020QC i = ck27020Q i := by
  unfold ck27020QC ck27020Q ckBodyQC ckBodyQ EVKC EVK prodKC prodK
  rewrite [pc27C_eq]
  exact rfl

theorem EVKC_eq : EVKC = EVK := by
  funext G GI wd
  unfold EVKC EVK
  rewrite [pc27C_eq]
  exact rfl

theorem prodKC_eq : prodKC = prodK := by
  funext E m
  unfold prodKC prodK
  rewrite [pc27C_eq]
  exact rfl

theorem ckBodyQC_eq : ckBodyQC = ckBodyQ := by
  funext I T A E F P
  unfold ckBodyQC ckBodyQ
  rewrite [pc27C_eq]
  exact rfl

theorem ck27020Q_of_tables {i : Fin 4} {T A : Fin 6 → Nat} {E : Fin 4 → Nat}
    (hT : ∀ j, EVK HYF HYF (hfxW i j) = T j) (hA : ∀ k, EVK T T (hsCommWord k) = A k)
    (hE : ∀ l, EVK HYF HYF (hfxE i l) = E l) (hF : ∀ l, EVK A A (hfxE i l) = E l)
    (hB : ckBodyQC idK T A E E (fun m => prodKC E m.val) = true) : ck27020Q i = true := by
  have hT' : Tk i = T := funext hT
  have hA' : Ak i = A := by
    funext k
    unfold Ak
    rewrite [hT']
    exact hA k
  have hE' : Ek i = E := funext hE
  have hF' : Fk i = E := by
    funext l
    unfold Fk
    rewrite [hA']
    exact hF l
  rewrite [ck_eq, hF', hA', hE', hT']
  rewrite [ckBodyQC_eq, prodKC_eq] at hB
  exact hB

theorem EVK_pin {G GI : Fin 6 → Nat} {wd : List (Fin 6 × Bool)} {v : Nat}
    (h : Nat.beq (EVKC G GI wd) v = true) : EVK G GI wd = v := by
  rewrite [← EVKC_eq]
  exact Nat.eq_of_beq_eq_true h

theorem ck27020Q_of_pins {i : Fin 4} {T A : Fin 6 → Nat} {E : Fin 4 → Nat}
    (hT0 : EVK HYF HYF (hfxW i 0) = T 0) (hT1 : EVK HYF HYF (hfxW i 1) = T 1)
    (hT2 : EVK HYF HYF (hfxW i 2) = T 2) (hT3 : EVK HYF HYF (hfxW i 3) = T 3)
    (hT4 : EVK HYF HYF (hfxW i 4) = T 4) (hT5 : EVK HYF HYF (hfxW i 5) = T 5)
    (hA0 : EVK T T (hsCommWord 0) = A 0) (hA1 : EVK T T (hsCommWord 1) = A 1)
    (hA2 : EVK T T (hsCommWord 2) = A 2) (hA3 : EVK T T (hsCommWord 3) = A 3)
    (hA4 : EVK T T (hsCommWord 4) = A 4) (hA5 : EVK T T (hsCommWord 5) = A 5)
    (hE0 : EVK HYF HYF (hfxE i 0) = E 0) (hE1 : EVK HYF HYF (hfxE i 1) = E 1)
    (hE2 : EVK HYF HYF (hfxE i 2) = E 2) (hE3 : EVK HYF HYF (hfxE i 3) = E 3)
    (hF0 : EVK A A (hfxE i 0) = E 0) (hF1 : EVK A A (hfxE i 1) = E 1)
    (hF2 : EVK A A (hfxE i 2) = E 2) (hF3 : EVK A A (hfxE i 3) = E 3)
    (hB : ckBodyQC idK T A E E (fun m => prodKC E m.val) = true) : ck27020Q i = true := by
  refine ck27020Q_of_tables ?_ ?_ ?_ ?_ hB
  · intro j
    fin_cases j
    exacts [hT0, hT1, hT2, hT3, hT4, hT5]
  · intro k
    fin_cases k
    exacts [hA0, hA1, hA2, hA3, hA4, hA5]
  · intro l
    fin_cases l
    exacts [hE0, hE1, hE2, hE3]
  · intro l
    fin_cases l
    exacts [hF0, hF1, hF2, hF3]

end CFSG.KD.TwoHS

end
