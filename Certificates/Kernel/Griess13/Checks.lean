module

public import Certificates.Kernel.Griess13.Data
public import CFSG.Certificates.Kernel.Griess13.PackedSound
public import CFSG.Certificates.Kernel.Griess13.SLPTextSound
public import Certificates.Kernel.Co1Cover.Bridge

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelG13

open CFSG.KC.G13 CFSG.KC.Co1B CFSG.KC.Co1F2 CertificateChecks.KernelCo1Cover
  CFSG.Monster.GMS.Griess13.Co1Data
open scoped Matrix

theorem parse_eq : parseSLP slpMax11 = slp := by
  rw [Slp.eq, charsEq_sound slp_text, parseSLP_slpC]

theorem prA_eq : prA = toPR (pk R0 R0) := by
  have h : dat.rowsA = unpackR 24 R0 := rowsA_eq
  simp only [prA, toPR, unpackR_pk, unpackR_sP_pk, h]

theorem prB_eq : prB = toPR (pk R1 G.B2) := by
  have h : dat.rowsB = unpackR 24 R1 := rowsB_eq
  have h2 : mulWK R1 R1 = G.B2 := Nat.eq_of_beq_eq_true b2_ok
  simp only [prB, toPR, unpackR_pk, unpackR_sP_pk, h, mulWK_unpack, h2]

theorem prNout_eq : prNout = [toPR G.N1, toPR G.N2] := by
  rw [prNout, parse_eq, prA_eq, prB_eq]
  change slp.evalPR ([pk R0 R0, pk R1 G.B2].map toPR) = _
  rw [evalPR_toPR, n_ok]
  rfl

theorem prN1_eq : prN1 = toPR G.N1 := by
  rw [prN1, prNout_eq]
  rfl

theorem prN2_eq : prN2 = toPR G.N2 := by
  rw [prN2, prNout_eq]
  rfl

theorem prWN_eq (s : String) : prWN s = toPR (wordP [G.N1, G.N2] (parseWord s)) := by
  rw [prWN, prN1_eq, prN2_eq]
  exact toPR_word [G.N1, G.N2] _

theorem prE_eq (i : Fin 6) : prE i = toPR (eK i) := by
  rw [prE, prWN_eq, e_ok]

theorem prTau_eq : prTau = toPR G.T := by
  rw [prTau, prWN_eq, t_ok]

theorem prM_eq (i : Fin 2) : prM i = toPR (mK i) := by
  rw [prM, prWN_eq, m_ok]

theorem prR_eq (k : Fin 12) : prR k = toPR (rK k) := by
  rw [prR, prWN_eq, r_ok]

theorem prNs_eq (s : Fin 2) : prNs s = toPR (nK s) := by
  fin_cases s
  · exact prN1_eq
  · exact prN2_eq

theorem prWM_eq (s : String) : prWM s = toPR (wordP [mK 0, mK 1] (parseWord s)) := by
  rw [prWM, prM_eq, prM_eq]
  exact toPR_word [mK 0, mK 1] _

theorem prIota_eq (v : Fin 6 → ZMod 3) : prIota v = toPR (iotaP eK fun i => (v i).val) :=
  prIota_toPR prE_eq v

@[expose] noncomputable def cmK : Nat := mulP (mulP (mulP (invP (mK 0)) (invP (mK 1))) (mK 0)) (mK 1)

@[expose] noncomputable def ccK (g : Nat) : Nat := mulP (mulP (invP g) cmK) g

@[expose] noncomputable def sK : List Nat :=
  [cmK, ccK (mK 0), ccK (mK 1), ccK (invP (mK 0)), ccK (invP (mK 1)), ccK (mulP (mK 0) (mK 1)),
    ccK (mulP (mK 1) (mK 0))]

theorem prS_eq : prS = sK.map toPR := by
  simp only [prS, prCConj, prCm, prM_eq, toPR_inv, toPR_mul, sK, ccK, cmK, List.map_cons, List.map_nil]

theorem commCheck_true : commCheck = true := by
  simp only [commCheck, prE_eq, toPR_mul, toPR_eq]
  decide +kernel

theorem cubeCheck_true : cubeCheck = true := by
  simp only [cubeCheck, prE_eq, toPR_pow, toPR_one, toPR_eq]
  decide +kernel

theorem iota_ne_one : ∀ v : Fin 6 → ZMod 3, v ≠ 0 → PR.eq (prIota v) PR.one = false :=
  iotaNe_sound prE_eq iotaNe_ok

theorem nConjCheck_true : nConjCheck = true := by
  simp only [nConjCheck, prNs_eq, prE_eq, toPR_conj, prIota_eq, toPR_eq]
  decide +kernel

theorem tauCheck_true : tauCheck = true := by
  simp only [tauCheck, prTau_eq, prE_eq, toPR_mul, toPR_conj, toPR_pow, toPR_one, prIota_eq, toPR_eq]
  decide +kernel

theorem mSCheck_true : mSCheck = true := by
  simp only [mSCheck, prM_eq, prS_eq, toPR_word, toPR_eq]
  decide +kernel

theorem mConjCheck_true : mConjCheck = true := by
  simp only [mConjCheck, prM_eq, prE_eq, toPR_conj, prIota_eq, toPR_eq]
  decide +kernel

theorem rConjCheck_true : rConjCheck = true := by
  simp only [rConjCheck, prR_eq, prE_eq, toPR_conj, prIota_eq, toPR_eq]
  decide +kernel

theorem decCheck_true : decCheck = true := by
  simp only [decCheck, prNs_eq, prR_eq, prE0, prIota_eq, toPR_pow, toPR_mul, prTau_eq, prWM_eq,
    toPR_eq]
  decide +kernel

theorem actP_w1 : ∀ i : Fin 2, actP i *ᵥ w1 = w1 := by decide +kernel

theorem actR_repw : ∀ k : Fin 12, ∃ c : ZMod 3, c ≠ 0 ∧ actR k *ᵥ repw k = c • w1 := by
  decide +kernel

theorem repw_zero : repw 0 = w1 := by decide +kernel

theorem w1_dotProduct_v0 : w1 ⬝ᵥ v0 = 1 := by decide +kernel

theorem decEps_le_one : ∀ (s : Fin 2) (k : Fin 12) (j : Fin 2), decEps s k j ≤ 1 := by decide +kernel

open Certificates in
open CFSG.Monster.GMS.Griess13.Co1Data in
open scoped Matrix in
theorem facts10032 :
    (commCheck = true)
    ∧ (cubeCheck = true)
    ∧ (∀ v : Fin 6 → ZMod 3, v ≠ 0 → PR.eq (prIota v) PR.one = false)
    ∧ (nConjCheck = true)
    ∧ (tauCheck = true)
    ∧ (mSCheck = true)
    ∧ (mConjCheck = true)
    ∧ (∀ i : Fin 2, actP i *ᵥ w1 = w1)
    ∧ (rConjCheck = true)
    ∧ (∀ k : Fin 12, ∃ c : ZMod 3, c ≠ 0 ∧ actR k *ᵥ repw k = c • w1)
    ∧ (repw 0 = w1)
    ∧ (w1 ⬝ᵥ v0 = 1)
    ∧ (decCheck = true)
    ∧ (∀ (s : Fin 2) (k : Fin 12) (j : Fin 2), decEps s k j ≤ 1) :=
  ⟨commCheck_true, cubeCheck_true, iota_ne_one, nConjCheck_true, tauCheck_true, mSCheck_true,
    mConjCheck_true, actP_w1, rConjCheck_true, actR_repw, repw_zero, w1_dotProduct_v0,
    decCheck_true, decEps_le_one⟩

end CertificateChecks.KernelG13

end
