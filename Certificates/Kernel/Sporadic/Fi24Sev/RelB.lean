module

public import Certificates.Kernel.Sporadic.Fi24Sev.DataB
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option Elab.async false

#kc_repo #kc_natLines CFSG.KD.Fi24SevB.Ck accD "Certificates/Kernel/Sporadic/Fi24Sev/data/relb.txt" 1290132 2770722710661752776

public section

namespace CFSG.KD.Fi24SevB.Ck

theorem qNe_t : CFSG.KD.Fi24SevB.qNe = true := by quickRfl
section

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO
  CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24SevB

theorem eqOK_cons {p : List Nat × List Nat} {ps : List (List Nat × List Nat)}
    (h1 : agB NW NT p.1 p.2 = true) (h2 : eqOK NW NT ps = true) : eqOK NW NT (p :: ps) = true := by
  change andB (agB NW NT p.1 p.2) (eqOK NW NT ps) = true
  rw [h1, h2]
  rfl

theorem qEq00 : agB NW NT (pw X (nat_lit 7)) [] = true := by quickRfl
theorem qEq01 : agB NW NT C (X ++ (Y ++ (pw X (nat_lit 6) ++ pw Y (nat_lit 6)))) = true := by
  quickRfl
theorem qEq02 : agB NW NT (C ++ X) (X ++ C) = true := by quickRfl
theorem qEq03 : agB NW NT (C ++ Y) (Y ++ C) = true := by quickRfl

theorem qEq_t : CFSG.KD.Fi24SevB.qEq = true :=
  eqOK_cons qEq00 <| eqOK_cons qEq01 <| eqOK_cons qEq02 <| eqOK_cons qEq03 rfl

theorem eEq00 : agB NW NT (pw uW (nat_lit 3)) [] = true := by quickRfl
theorem eEq01 : agB NW NT (pw vW (nat_lit 3)) [] = true := by quickRfl
theorem eEq02 : agB NW NT (uW ++ vW) (vW ++ uW) = true := by quickRfl
theorem eEq03 : agB NW NT uvW (uW ++ vW) = true := by quickRfl
theorem eEq04 : agB NW NT uv2W (uW ++ (vW ++ vW)) = true := by quickRfl
theorem eEq05 : agB NW NT (uW ++ Y) (Y ++ uW) = true := by quickRfl
theorem eEq06 : agB NW NT (vW ++ Y) (Y ++ vW) = true := by quickRfl
theorem eEq07 : agB NW NT (pw u4W (nat_lit 4)) [] = true := by quickRfl
theorem eEq08 : agB NW NT (u4W ++ Y) (Y ++ u4W) = true := by quickRfl
theorem eEq09 : agB NW NT (pw u2W (nat_lit 2)) [] = true := by quickRfl
theorem eEq10 : agB NW NT (u2W ++ C) (C ++ u2W) = true := by quickRfl
theorem eEq11 : agB NW NT (pw u3W (nat_lit 3)) [] = true := by quickRfl
theorem eEq12 : agB NW NT (u3W ++ C) (C ++ u3W) = true := by quickRfl
theorem eEq13 : agB NW NT (u2W ++ X) (pw X (nat_lit 6) ++ u2W) = true := by quickRfl
theorem eEq14 : agB NW NT (u2W ++ Y) (pw Y (nat_lit 6) ++ (pw C (nat_lit 6) ++ u2W)) = true := by
  quickRfl
theorem eEq15 : agB NW NT (u3W ++ X) (pw X (nat_lit 4) ++ u3W) = true := by quickRfl
theorem eEq16 : agB NW NT (u3W ++ Y) (pw Y (nat_lit 2) ++ (pw C (nat_lit 4) ++ u3W)) = true := by
  quickRfl

theorem eEq_t : CFSG.KD.Fi24SevB.eEq = true :=
  eqOK_cons eEq00 <| eqOK_cons eEq01 <| eqOK_cons eEq02 <| eqOK_cons eEq03 <| eqOK_cons eEq04 <|
  eqOK_cons eEq05 <| eqOK_cons eEq06 <| eqOK_cons eEq07 <| eqOK_cons eEq08 <| eqOK_cons eEq09 <|
  eqOK_cons eEq10 <| eqOK_cons eEq11 <| eqOK_cons eEq12 <| eqOK_cons eEq13 <| eqOK_cons eEq14 <|
  eqOK_cons eEq15 <| eqOK_cons eEq16 rfl

end
theorem eNe_t : CFSG.KD.Fi24SevB.eNe = true := by quickRfl

section
open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24ThreeO CFSG.KC.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit
  CFSG.KD.Fi24SevB

noncomputable def fixRest (F : Nat → Nat) (P0 s k m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) s
    (fun j acc => strictN acc (fun a => Fi24FixP.fixStep F P0 (Nat.add k j) a)) m

theorem fixAcc_add (F : Nat → Nat) (P0 k : Nat) :
    ∀ m, Fi24FixP.fixAcc F P0 (Nat.add k m) = fixRest F P0 (Fi24FixP.fixAcc F P0 k) k m
  | 0 => rfl
  | m + 1 => by
    change strictN (Fi24FixP.fixAcc F P0 (Nat.add k m)) (fun a => Fi24FixP.fixStep F P0 (Nat.add k m) a) =
      strictN (fixRest F P0 (Fi24FixP.fixAcc F P0 k) k m) (fun a => Fi24FixP.fixStep F P0 (Nat.add k m) a)
    rw [fixAcc_add F P0 k m]

theorem strictN_fix (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

noncomputable abbrev fixP0 (w : List Nat) : Nat := wkC NW NT w (Fi24FixP.idPl19 (nat_lit 0))

noncomputable def fixPA (w : List Nat) (A : Nat) : Bool :=
  Nat.beq (strictN (fixP0 w) fun P0 => Fi24FixP.fixAcc (wkC NW NT w) P0 (nat_lit 7)) A

noncomputable def fixPB (w : List Nat) (A B : Nat) : Bool :=
  Nat.beq (strictN (fixP0 w) fun P0 => fixRest (wkC NW NT w) P0 A (nat_lit 7) (nat_lit 6)) B

noncomputable def fixPC (w : List Nat) (B n : Nat) : Bool :=
  Nat.beq (popcount (strictN (fixP0 w) fun P0 => fixRest (wkC NW NT w) P0 B (nat_lit 13) (nat_lit 6))
    (nat_lit 524288)) n

theorem fixK_of3 {w : List Nat} {n A B : Nat} (h1 : fixPA w A = true) (h2 : fixPB w A B = true)
    (h3 : fixPC w B n = true) : fixK NW NT w n = true := by
  unfold fixPA at h1
  unfold fixPB at h2
  unfold fixPC at h3
  rw [strictN_fix] at h1 h2 h3
  have e13 : Fi24FixP.fixAcc (wkC NW NT w) (fixP0 w) (nat_lit 13) = B := by
    rw [fixAcc_add _ _ (nat_lit 7) (nat_lit 6), Nat.eq_of_beq_eq_true h1]
    exact Nat.eq_of_beq_eq_true h2
  have e19 : Fi24FixP.fixAcc (wkC NW NT w) (fixP0 w) (nat_lit 19) =
      fixRest (wkC NW NT w) (fixP0 w) B (nat_lit 13) (nat_lit 6) := by
    rw [fixAcc_add _ _ (nat_lit 13) (nat_lit 6), e13]
  change Nat.beq (popcount (strictN (fixP0 w) fun P0 => Fi24FixP.fixAcc (wkC NW NT w) P0 (nat_lit 19))
    (nat_lit 524288)) n = true
  rw [strictN_fix, e19]
  exact h3

theorem fU_a : fixPA uW accD.n0 = true := by quickRfl
theorem fU_b : fixPB uW accD.n0 accD.n1 = true := by quickRfl
theorem fU_c : fixPC uW accD.n1 (nat_lit 0) = true := by quickRfl
theorem fU_t : CFSG.KD.Fi24SevB.fU = true := fixK_of3 fU_a fU_b fU_c

theorem fV_a : fixPA vW accD.n2 = true := by quickRfl
theorem fV_b : fixPB vW accD.n2 accD.n3 = true := by quickRfl
theorem fV_c : fixPC vW accD.n3 (nat_lit 0) = true := by quickRfl
theorem fV_t : CFSG.KD.Fi24SevB.fV = true := fixK_of3 fV_a fV_b fV_c

theorem fUV_a : fixPA uvW accD.n4 = true := by quickRfl
theorem fUV_b : fixPB uvW accD.n4 accD.n5 = true := by quickRfl
theorem fUV_c : fixPC uvW accD.n5 (nat_lit 3240) = true := by quickRfl
theorem fUV_t : CFSG.KD.Fi24SevB.fUV = true := fixK_of3 fUV_a fUV_b fUV_c

theorem fUV2_a : fixPA uv2W accD.n6 = true := by quickRfl
theorem fUV2_b : fixPB uv2W accD.n6 accD.n7 = true := by quickRfl
theorem fUV2_c : fixPC uv2W accD.n7 (nat_lit 3240) = true := by quickRfl
theorem fUV2_t : CFSG.KD.Fi24SevB.fUV2 = true := fixK_of3 fUV2_a fUV2_b fUV2_c

theorem fU3_a : fixPA u3W accD.n8 = true := by quickRfl
theorem fU3_b : fixPB u3W accD.n8 accD.n9 = true := by quickRfl
theorem fU3_c : fixPC u3W accD.n9 (nat_lit 378) = true := by quickRfl
theorem fU3_t : CFSG.KD.Fi24SevB.fU3 = true := fixK_of3 fU3_a fU3_b fU3_c

theorem fY_a : fixPA Y accD.n10 = true := by quickRfl
theorem fY_b : fixPB Y accD.n10 accD.n11 = true := by quickRfl
theorem fY_c : fixPC Y accD.n11 (nat_lit 21) = true := by quickRfl
theorem fY_t : CFSG.KD.Fi24SevB.fY = true := fixK_of3 fY_a fY_b fY_c

theorem fC_a : fixPA C accD.n12 = true := by quickRfl
theorem fC_b : fixPB C accD.n12 accD.n13 = true := by quickRfl
theorem fC_c : fixPC C accD.n13 (nat_lit 0) = true := by quickRfl
theorem fC_t : CFSG.KD.Fi24SevB.fC = true := fixK_of3 fC_a fC_b fC_c

end

end CFSG.KD.Fi24SevB.Ck

end
