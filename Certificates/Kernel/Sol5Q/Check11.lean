module

public import Certificates.Kernel.Sol5Q.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Sol5Q11

open CFSG.KC.Sol5Q
open CFSG.KC.BalanceSC (notB)

theorem ct : ctOK (nat_lit 11) S (nat_lit 2304) CT = true := by quickRfl

theorem h : hOK (nat_lit 11) E HB NH HG HPL = true := by quickRfl

theorem gens : gensK (nat_lit 11) E S HG = true := by quickRfl

theorem fcb : fcbK (nat_lit 11) E HB NH BN CT RB = true := by quickRfl

@[expose] noncomputable def fcrKG (n e S HB NH : Nat) (big : Bool) (BN ctx CT : List Nat)
    (RR : List (List Nat)) (GD : List (List Nat × List Nat × List Nat × List Nat)) : Bool :=
  List.rec
    (motive := fun _ => List (List Nat) → List (List Nat × List Nat × List Nat × List Nat) → Bool)
    (fun RR GD => bAnd(emptyL RR, emptyL GD))
    (fun x _ ih RR GD => List.rec (motive := fun _ => Bool) false (fun r RR' _ =>
      List.rec (motive := fun _ => Bool) false (fun t rest _ =>
        bIf(Nat.beq t (nat_lit 0), bAnd(notB (Nat.beq (pw n e x (nat_lit 8)) e), ih RR' GD),
        bIf(Nat.beq t (nat_lit 1), bAnd(bIf(Nat.beq x e, true, Nat.beq x S), ih RR' GD),
        bIf(Nat.beq t (nat_lit 2), bAnd(allL rest (fun c => Nat.ble c NH),
            bAnd(badK n e (prodK n e S HB x rest), ih RR' GD)),
          List.rec (motive := fun _ => Bool) false
            (fun g GD' _ => bAnd(goodK n e HB NH big BN ctx x rest g, ih RR' GD')) GD)))) r) RR)
    CT RR GD

theorem brec_tt {x y : Bool} (h : Bool.rec (motive := fun _ => Bool) false y x = true) :
    x = true ∧ y = true := by
  cases x <;> cases y
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, rfl⟩

theorem emptyL_nil {α : Type} {L : List α} (h : emptyL L = true) : L = [] := by
  cases L
  · rfl
  · exact absurd h Bool.false_ne_true

theorem fcrKG_append {n e S HB NH : Nat} {big : Bool} {BN ctx : List Nat} (CT₂ : List Nat)
    (RR₂ : List (List Nat)) (GD₂ : List (List Nat × List Nat × List Nat × List Nat))
    (h₂ : fcrKG n e S HB NH big BN ctx CT₂ RR₂ GD₂ = true) :
    ∀ (CT₁ : List Nat) (RR₁ : List (List Nat))
      (GD₁ : List (List Nat × List Nat × List Nat × List Nat)),
      fcrKG n e S HB NH big BN ctx CT₁ RR₁ GD₁ = true →
      fcrKG n e S HB NH big BN ctx (CT₁ ++ CT₂) (RR₁ ++ RR₂) (GD₁ ++ GD₂) = true
  | [], RR₁, GD₁, h => by
    obtain ⟨e1, e2⟩ := brec_tt h
    rw [emptyL_nil e1, emptyL_nil e2]
    exact h₂
  | x :: CT₁, RR₁, GD₁, h => by
    have ih := fcrKG_append CT₂ RR₂ GD₂ h₂ CT₁
    match RR₁, h with
    | [], h => exact absurd h Bool.false_ne_true
    | [] :: RR₁, h => exact absurd h Bool.false_ne_true
    | (t :: rest) :: RR₁, h =>
      change bIf(Nat.beq t (nat_lit 0),
          bAnd(notB (Nat.beq (pw n e x (nat_lit 8)) e), fcrKG n e S HB NH big BN ctx CT₁ RR₁ GD₁),
        bIf(Nat.beq t (nat_lit 1),
          bAnd(bIf(Nat.beq x e, true, Nat.beq x S), fcrKG n e S HB NH big BN ctx CT₁ RR₁ GD₁),
        bIf(Nat.beq t (nat_lit 2), bAnd(allL rest (fun c => Nat.ble c NH),
            bAnd(badK n e (prodK n e S HB x rest), fcrKG n e S HB NH big BN ctx CT₁ RR₁ GD₁)),
          List.rec (motive := fun _ => Bool) false
            (fun g GD' _ => bAnd(goodK n e HB NH big BN ctx x rest g,
              fcrKG n e S HB NH big BN ctx CT₁ RR₁ GD')) GD₁))) = true at h
      change bIf(Nat.beq t (nat_lit 0),
          bAnd(notB (Nat.beq (pw n e x (nat_lit 8)) e),
            fcrKG n e S HB NH big BN ctx (CT₁ ++ CT₂) (RR₁ ++ RR₂) (GD₁ ++ GD₂)),
        bIf(Nat.beq t (nat_lit 1), bAnd(bIf(Nat.beq x e, true, Nat.beq x S),
            fcrKG n e S HB NH big BN ctx (CT₁ ++ CT₂) (RR₁ ++ RR₂) (GD₁ ++ GD₂)),
        bIf(Nat.beq t (nat_lit 2), bAnd(allL rest (fun c => Nat.ble c NH),
            bAnd(badK n e (prodK n e S HB x rest),
              fcrKG n e S HB NH big BN ctx (CT₁ ++ CT₂) (RR₁ ++ RR₂) (GD₁ ++ GD₂))),
          List.rec (motive := fun _ => Bool) false
            (fun g GD' _ => bAnd(goodK n e HB NH big BN ctx x rest g,
              fcrKG n e S HB NH big BN ctx (CT₁ ++ CT₂) (RR₁ ++ RR₂) GD'))
            (GD₁ ++ GD₂)))) = true
      revert h
      cases Nat.beq t 0
      · cases Nat.beq t 1
        · cases Nat.beq t 2
          · intro h
            match GD₁, h with
            | [], h => exact absurd h Bool.false_ne_true
            | g :: GD₁, h =>
              obtain ⟨h1, h2⟩ := brec_tt h
              show bAnd(goodK n e HB NH big BN ctx x rest g, fcrKG n e S HB NH big BN ctx
                (CT₁ ++ CT₂) (RR₁ ++ RR₂) (GD₁ ++ GD₂)) = true
              rw [h1, ih RR₁ GD₁ h2]
          · intro h
            obtain ⟨h1, h2⟩ := brec_tt h
            obtain ⟨h21, h22⟩ := brec_tt h2
            show bAnd(allL rest (fun c => Nat.ble c NH), bAnd(badK n e (prodK n e S HB x rest),
              fcrKG n e S HB NH big BN ctx (CT₁ ++ CT₂) (RR₁ ++ RR₂)
                (GD₁ ++ GD₂))) = true
            rw [h1, h21, ih RR₁ GD₁ h22]
        · intro h
          obtain ⟨h1, h2⟩ := brec_tt h
          show bAnd(bIf(Nat.beq x e, true, Nat.beq x S),
            fcrKG n e S HB NH big BN ctx (CT₁ ++ CT₂) (RR₁ ++ RR₂) (GD₁ ++ GD₂)) = true
          rw [h1, ih RR₁ GD₁ h2]
      · intro h
        obtain ⟨h1, h2⟩ := brec_tt h
        show bAnd(notB (Nat.beq (pw n e x (nat_lit 8)) e),
          fcrKG n e S HB NH big BN ctx (CT₁ ++ CT₂) (RR₁ ++ RR₂) (GD₁ ++ GD₂)) = true
        rw [h1, ih RR₁ GD₁ h2]

theorem fcrK_eq_fcrKG (n e S HB NH : Nat) (big : Bool) (BN CT : List Nat) (RR : List (List Nat))
    (GD : List (List Nat × List Nat × List Nat × List Nat)) :
    fcrK n e S HB NH big BN CT RR GD = fcrKG n e S HB NH big BN CT CT RR GD := rfl

theorem fcrA : fcrKG (nat_lit 11) E S HB NH true BN CT
    (CT.take 768)
    (RR.take 768)
    [] = true := by
  quickRfl

theorem fcrB : fcrKG (nat_lit 11) E S HB NH true BN CT
    ((CT.drop 768).take 768)
    ((RR.drop 768).take 768)
    [] = true := by
  quickRfl

theorem fcrC : fcrKG (nat_lit 11) E S HB NH true BN CT
    (((CT.drop 768).drop 768).take 387)
    (((RR.drop 768).drop 768).take 387)
    [] = true := by
  quickRfl

theorem fcrD : fcrKG (nat_lit 11) E S HB NH true BN CT
    ((((CT.drop 768).drop 768).drop 387).take 100)
    ((((RR.drop 768).drop 768).drop 387).take 100)
    (GD.take 4) = true := by
  quickRfl

theorem fcrE : fcrKG (nat_lit 11) E S HB NH true BN CT
    (((((CT.drop 768).drop 768).drop 387).drop 100).take 130)
    (((((RR.drop 768).drop 768).drop 387).drop 100).take 130)
    ((GD.drop 4).take 4) = true := by
  quickRfl

theorem fcrF : fcrKG (nat_lit 11) E S HB NH true BN CT
    (((((CT.drop 768).drop 768).drop 387).drop 100).drop 130)
    (((((RR.drop 768).drop 768).drop 387).drop 100).drop 130)
    ((GD.drop 4).drop 4) = true := by
  quickRfl

theorem fcr : fcrK (nat_lit 11) E S HB NH true BN CT RR GD = true := by
  have hEF := fcrKG_append _ _ _ fcrF _ _ _ fcrE
  rw [List.take_append_drop, List.take_append_drop, List.take_append_drop] at hEF
  have hD := fcrKG_append _ _ _ hEF _ _ _ fcrD
  rw [List.take_append_drop, List.take_append_drop, List.take_append_drop] at hD
  have hC := fcrKG_append _ _ _ hD _ _ _ fcrC
  rw [List.take_append_drop, List.take_append_drop, List.nil_append] at hC
  have hB := fcrKG_append _ _ _ hC _ _ _ fcrB
  rw [List.take_append_drop, List.take_append_drop, List.nil_append] at hB
  have hA := fcrKG_append _ _ _ hB _ _ _ fcrA
  rw [List.take_append_drop, List.take_append_drop, List.nil_append] at hA
  rw [fcrK_eq_fcrKG]
  exact hA

theorem fco2 : fco2K (nat_lit 11) E HB NH true FO = true := by quickRfl

end CFSG.KD.Sol5Q11
