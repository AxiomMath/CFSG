module

public import Certificates.Kernel.Misc.Sp6Over.Checks
public import CFSG.Certificates.Kernel.Misc.Sp6OverSound

public section

namespace CFSG.KC.Sp6Over

open CFSG.KD.Sp6Over CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
  CFSG.Quasithin.G2U
open scoped Matrix

theorem hdr_REC : HdrOK REC := by decide +kernel

theorem ov_h6_facts :
    pairCheck (ovGamC, ovGamI) = true ∧ pairCheck (ovHC, ovHI) = true ∧
    pairCheck (ovCC, ovCI) = true ∧ relW.all (fun r => powCode (wordC r.1) r.2 == one6) = true ∧
    powCode ovGamC 7 = one6 ∧ ovGamC ≠ one6 ∧ powCode ovHC 6 = one6 ∧
    mul6 ovHC ovGamC = mul6 (powCode ovGamC 3) ovHC ∧
    mul6 ovCC (mul6 ovHC ovHC) = mul6 (mul6 ovHC ovHC) ovCC ∧
    wordC wZ0 = zCode 0 ∧ wordC wZ1 = zCode 1 ∧ wordC wT = tCode ∧
    wS.map wordC = sylowP.map Prod.fst ∧ powCode (wordC [0, 1, 2]) 5 = one6 ∧
    wordC [0, 1, 2] ≠ one6 :=
  h6_facts hdr_REC ov_h6_ok

theorem pinHdr_REC : PinHdr REC := by decide +kernel

theorem ov_pin_facts :
    (∀ c < 128, CFSG.Quasithin.H13.MatNCert.mvN n2c c = c → c ∈ fixL) ∧
    (∀ c < 128, CFSG.Quasithin.H13.MatNCert.mvN n2c (CFSG.Quasithin.H13.MatNCert.mvN n2c c) =
      (c ^^^ CFSG.Quasithin.H13.MatNCert.mvN n2c c) → c ∈ wL) ∧
    (∀ a ∈ fixL, ∀ u ∈ wL, ∀ b ∈ fixL, ∀ v ∈ wL,
      relsOK (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v) = true →
      CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v = xSc ∨
        CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v = xIc) :=
  pin_facts hdr_REC pinHdr_REC ov_pin_ok

theorem matHdr_REC : MatHdr REC := by decide +kernel

theorem ov_k_facts {x : List ℕ} (hx : x = xSc ∨ x = xIc) :
    (∀ m, 0 < m → m < 64 → ∃ s ∈ CFSG.Quasithin.H13.MatNCert.genSubN 7 [nGc, nHc, x],
      CFSG.Quasithin.H13.MatNCert.decN 7 (kC m) =
        ((s : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
        CFSG.Quasithin.H13.MatNCert.decN 7 (kC 1) *
        ((s⁻¹ : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))) ∧
    ((List.range 128).filter fun v =>
      CFSG.Quasithin.H13.MatNCert.mvN (bbarC x) v == v).length = 32 ∧
    (∀ g ∈ rGens x, CFSG.Quasithin.H13.MatNCert.mulN g (bbarC x) =
      CFSG.Quasithin.H13.MatNCert.mulN (bbarC x) g) ∧
    (∀ m ∈ [6, 8, 17, 33], CFSG.Quasithin.H13.MatNCert.mulN (kC m) (kC m) =
      CFSG.Quasithin.H13.MatNCert.oneN 7) ∧
    Nat.card (CFSG.Quasithin.H13.MatNCert.genSubN 7 (rGens x)) = 32 :=
  k_facts hdr_REC pinHdr_REC ov_k_ok hx

theorem ov_u_facts : piC xIc = piC xSc ∧
    (∀ u ∈ uGens, CFSG.Quasithin.H13.MatNCert.mulN u u = CFSG.Quasithin.H13.MatNCert.oneN 6 ∧
      CFSG.Quasithin.H13.MatNCert.mulN u pibbarC = CFSG.Quasithin.H13.MatNCert.mulN pibbarC u) ∧
    Nat.card (CFSG.Quasithin.H13.MatNCert.genSubN 6 uGens) = 32 :=
  u_facts hdr_REC pinHdr_REC matHdr_REC ov_u_ok

theorem formHdr_REC : FormHdr REC := by decide +kernel

theorem ov_lanes : ∀ s < 3, laneOK (tabAll REC) s (REC s) = true := by decide +kernel

theorem ov_lanes_grs : ∀ r < 5, laneOK (tabs (REC (3 + r))) 0 (REC (3 + r)) = true := by
  decide +kernel

theorem ov_form_facts :
    (∀ g ∈ sbGens, (CFSG.Quasithin.H13.MatNCert.decN 6 g)ᵀ *
      CFSG.Quasithin.H13.MatNCert.decN 6 w0c * CFSG.Quasithin.H13.MatNCert.decN 6 g =
        CFSG.Quasithin.H13.MatNCert.decN 6 w0c) ∧
    (∀ g ∈ sbGens ++ grs, ∃ u : GL (Fin 6) (ZMod 2),
      (u : Mat6) = CFSG.Quasithin.H13.MatNCert.decN 6 g) ∧
    ∃ T : ℕ → List Mat6, T 0 = [CFSG.Quasithin.H13.MatNCert.decN 6 w0c] ∧
      (∀ r < 5, (T (r + 1)).length = [315, 2880, 2880, 3780, 4032].getD r 0) ∧
      ((List.range 6).flatMap T).Nodup ∧
      ∀ r < 5, ∀ x ∈ T (r + 1), ∃ u : GL (Fin 6) (ZMod 2),
        (u : Mat6) = CFSG.Quasithin.H13.MatNCert.decN 6 (grs.getD r []) ∧
        ∃ s ∈ CFSG.Quasithin.H13.MatNCert.genSubN 6 sbGens,
          x = ((u * s : GL (Fin 6) (ZMod 2)) : Mat6)ᵀ *
            CFSG.Quasithin.H13.MatNCert.decN 6 w0c * ((u * s : GL (Fin 6) (ZMod 2)) : Mat6) :=
  form_facts matHdr_REC formHdr_REC (by decide +kernel) (by decide +kernel) ov_lanes
    ov_lanes_grs ov_form_ok

end CFSG.KC.Sp6Over

end
