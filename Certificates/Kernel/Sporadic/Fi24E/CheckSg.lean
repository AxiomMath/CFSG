module

public import Certificates.Kernel.Sporadic.Fi24E.Data
public import Certificates.Kernel.Sporadic.Fi24ThreeO.Facts
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KD.Fi24E.Ck

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt
  CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Oct CFSG.KC.Fi24E CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt
  CFSG.KS.Fi24Kit CFSG.KS.Fi24ThreeO CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO CFSG.KD.Fi24Oct
  CFSG.KD.Fi24E

@[expose] noncomputable def fxDW (FT : Nat) (W : List Nat) : Nat := Nat.land (ctP NW NT FT W) ptsM

@[expose] noncomputable def sigsT (FT : Nat) (ws : List (List Nat)) (p q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (Nat.lor ptsM (Nat.shiftLeft ptsM (nat_lit 524288)))
    (fun w _ ih => strictN ih (fun a => strictN (fxDW FT w) (fun F =>
      Nat.land a (Nat.lor (same F p) (Nat.shiftLeft (same F q) (nat_lit 524288)))))) ws

@[expose] noncomputable def passOKT (FT : Nat) (ws : List (List Nat)) (p q : Nat) (W0 tv : List Nat)
    (pp : List (Nat × Nat)) (n P : Nat) : Bool :=
  andB (Nat.beq (popcount (Nat.land P (ones (nat_lit 524288))) (nat_lit 524288)) n)
    (andB (letB (fxDW FT W0) (fun F =>
        letB (cutP NW NT ws F q (Nat.shiftRight P (nat_lit 524288)) tv) (fun C =>
          Nat.beq (Nat.land C (pl1 pp)) C)))
      (ppOK NW NT ws p q pp))

@[expose] noncomputable def sigOKT (FT : Nat) (ws : List (List Nat)) (p q : Nat) (W0 tv : List Nat)
    (pp : List (Nat × Nat)) (n : Nat) : Bool :=
  letB (sigsT FT ws p q) (passOKT FT ws p q W0 tv pp n)

theorem sgT_t : sigOKT (fixC NW NT [nat_lit 26]) wcs p1 p2 [nat_lit 0] tv pp sig1 = true := by
  quickRfl

theorem invCE_append : ∀ (u v : List Nat), invC (u ++ v) = invC v ++ invC u
  | [], v => by rw [List.nil_append]; exact (List.append_nil _).symm
  | c :: u, v => by
    rw [List.cons_append, invC_cons, invCE_append u v, invC_cons, List.append_assoc]

theorem invCE_invC : ∀ {W : List Nat}, (∀ c ∈ W, c < 26) → invC (invC W) = W
  | [], _ => rfl
  | c :: W, h => by
    have hc := h c List.mem_cons_self
    rw [invC_cons, invCE_append, invCE_invC (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))]
    change invC [nIf(Nat.beq c (nat_lit 26), nat_lit 26, Nat.xor c (nat_lit 1))] ++ W = c :: W
    rw [invC_cons]
    interval_cases c <;> rfl

theorem cPE_invC {W : List Nat} (hW : ∀ c ∈ W, c < 26) (x : Nat) :
    cP NW NT W (cP NW NT (invC W) x) = x := by
  have h := cP_invC (invC_lt hW) x
  rwa [invCE_invC hW] at h

theorem cP_dW_iff {W : List Nat} (hW : ∀ c ∈ W, c < 26) (x : Nat) :
    cP NW NT (dW W) x = x ↔ pF NT (cP NW NT (invC W) x) = cP NW NT (invC W) x := by
  have e : cP NW NT (dW W) x = cP NW NT W (pF NT (cP NW NT (invC W) x)) := by
    change cP NW NT (W ++ (26 :: invC W)) x = _
    rw [cP_append, cP_cons]
    rfl
  rw [e]
  constructor
  · intro h
    have h2 := congrArg (cP NW NT (invC W)) h
    rwa [cP_invC hW] at h2
  · intro h
    rw [h, cPE_invC hW]

theorem fixC_dW {W : List Nat} (hW : ∀ c ∈ W, c < 26) :
    fixC NW NT (dW W) = fxDW (fixC NW NT [nat_lit 26]) W := by
  refine Nat.eq_of_testBit_eq fun x => ?_
  have hn : ∀ a b : Nat, Nat.land a b = a &&& b := fun _ _ => rfl
  unfold fxDW ctP
  rw [hn, Nat.testBit_and]
  by_cases hx : x < 306936
  · rw [ptsM_bit hx, Bool.and_true, testBit_wkC vn _ _ (by omega)]
    refine Bool.eq_iff_iff.2 ?_
    rw [testBit_fixC vn, fixT_iff, cP_dW_iff hW]
    have hl : ∀ c ∈ invC W, c ≤ 26 := fun c hc => by
      have := invC_lt hW c hc
      omega
    exact ⟨fun h => ⟨cP_pts hl hx, h.2⟩, fun h => ⟨hx, h.2⟩⟩
  · rw [ptsM_bit' hx, Bool.and_false]
    cases e : (fixC NW NT (dW W)).testBit x
    · rfl
    · exact absurd ((testBit_fixC vn _ x).1 e).1 hx

theorem sigs_eqT {p q : Nat} :
    ∀ {ws : List (List Nat)}, (∀ w ∈ ws, ∀ c ∈ w, c < 26) →
      sigs NW NT ws p q = sigsT (fixC NW NT [nat_lit 26]) ws p q
  | [], _ => rfl
  | w :: ws, h => by
    have e1 : sigs NW NT (w :: ws) p q = strictN (sigs NW NT ws p q) (fun a =>
        strictN (fixC NW NT (dW w)) (fun F =>
          Nat.land a (Nat.lor (same F p) (Nat.shiftLeft (same F q) (nat_lit 524288))))) := rfl
    have e2 : sigsT (fixC NW NT [nat_lit 26]) (w :: ws) p q =
        strictN (sigsT (fixC NW NT [nat_lit 26]) ws p q) (fun a =>
          strictN (fxDW (fixC NW NT [nat_lit 26]) w) (fun F =>
            Nat.land a (Nat.lor (same F p) (Nat.shiftLeft (same F q) (nat_lit 524288))))) := rfl
    rw [e1, e2, sigs_eqT (fun w' hw' => h w' (List.mem_cons_of_mem w hw')),
      fixC_dW (h w List.mem_cons_self)]

theorem sigOK_eqT {ws : List (List Nat)} {p q : Nat} {W0 tv : List Nat} {pp : List (Nat × Nat)}
    {n : Nat} (hws : ∀ w ∈ ws, ∀ c ∈ w, c < 26) (hW0 : ∀ c ∈ W0, c < 26) :
    sigOK NW NT ws p q (dW W0) tv pp n = sigOKT (fixC NW NT [nat_lit 26]) ws p q W0 tv pp n := by
  have e : passOK NW NT ws p q (dW W0) tv pp n =
      passOKT (fixC NW NT [nat_lit 26]) ws p q W0 tv pp n := funext fun P => by
    unfold passOK passOKT
    rw [fixC_dW hW0]
  unfold sigOK sigOKT
  rw [sigs_eqT hws, e]

theorem wcs_lt : ∀ w ∈ wcs, ∀ c ∈ w, c < 26 := by decide

theorem sg_t : sg = true :=
  (sigOK_eqT wcs_lt (by decide)).trans sgT_t

end CFSG.KD.Fi24E.Ck

end
