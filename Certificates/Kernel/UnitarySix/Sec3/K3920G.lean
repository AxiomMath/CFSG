module

public import Certificates.Kernel.UnitarySix.Sec3.K3920
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.EvenSmallLie.UnitarySix.YamadaHAut
open CFSG.RankThree.Native

theorem hdT : dTab = unpack 693 10 (dPK 1) := dArr_unpack (q := 1) (by norm_num)
theorem hsT : sTab = unpack 693 10 (dPK 3) := dArr_unpack (q := 3) (by norm_num)

theorem kBasic : (Nat.beq (pcomp 693 10 (mask 10) (dPK 1) (dPK 2)) (pidn 693 10) &&
    Nat.beq (pcomp 693 10 (mask 10) (dPK 3) (dPK 3)) (pidn 693 10) &&
    Nat.beq (pcomp 693 10 (mask 10) (pcomp 693 10 (mask 10) (dPK 3) (dPK 1))
      (pcomp 693 10 (mask 10) (dPK 3) (dPK 1))) (pidn 693 10)) = true := by
  decide +kernel

theorem basic_k : basicCheck = true := by
  have hk := kBasic
  simp only [Bool.and_eq_true] at hk
  have c := fun q (hq : q < 6) => dPK_canon q hq
  unfold basicCheck
  have h2 : d2Tab = unpack 693 10 (dPK 2) := dArr_unpack (q := 2) (by norm_num)
  rw [hdT, hsT, h2, comp_unpack (c 1 (by norm_num)) (c 2 (by norm_num)),
    comp_unpack (c 3 (by norm_num)) (c 3 (by norm_num)),
    comp_unpack (c 3 (by norm_num)) (c 1 (by norm_num)),
    comp_unpack (canon_comp (c 3 (by norm_num)) (c 1 (by norm_num)))
      (canon_comp (c 3 (by norm_num)) (c 1 (by norm_num))), hidA,
    eq_unpack (canon_comp (c 1 (by norm_num)) (c 2 (by norm_num))) hid,
    eq_unpack (canon_comp (c 3 (by norm_num)) (c 3 (by norm_num))) hid,
    eq_unpack (canon_comp (canon_comp (c 3 (by norm_num)) (c 1 (by norm_num)))
      (canon_comp (c 3 (by norm_num)) (c 1 (by norm_num)))) hid,
    PermK.valid (dPK_perm 1 (by norm_num)), PermK.valid (dPK_perm 3 (by norm_num))]
  simp only [Bool.and_eq_true, Bool.true_and]
  exact ⟨⟨hk.1.1, hk.1.2⟩, hk.2⟩

@[expose] noncomputable def sfL (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CL.LR CL.TRI CL.BP 5 0 G

theorem kOuter : ((List.range 5).all fun q => !(sfL (dPK (q + 1)))) = true := by decide +kernel

theorem chX2_P : ∀ j < chX2.gens.length, PermK (CX2.S j) (CX2.SI j) = true := by decide +kernel
theorem chSJ_P : ∀ j < chSJ.gens.length, PermK (CSJ.S j) (CSJ.SI j) = true := by decide +kernel
theorem chX8_P : ∀ j < chX8.gens.length, PermK (CX8.S j) (CX8.SI j) = true := by decide +kernel
theorem chZ_P : ∀ j < chZ.gens.length, PermK (CZ.S j) (CZ.SI j) = true := by decide +kernel
theorem chX1Z_P : ∀ j < chX1Z.gens.length, PermK (CX1Z.S j) (CX1Z.SI j) = true := by
  decide +kernel
theorem chL_P : ∀ j < chL.gens.length, PermK (CL.S j) (CL.SI j) = true := by decide +kernel
theorem chK2A2_P : ∀ j < chK2A2.gens.length, PermK (CK2A2.S j) (CK2A2.SI j) = true := by
  decide +kernel

@[expose] noncomputable def normByK (n nb : ℕ) (PS LR TRI : ℕ → ℕ) (BP : ℕ) : Bool :=
  (List.range n).all fun i =>
    siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) LR TRI BP nb 0
      (pcomp 693 10 (mask 10) (dPK 1) (pcomp 693 10 (mask 10) (PS i)
        (pinvS 693 10 (mask 10) (dPK 1)))) &&
    siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) LR TRI BP nb 0
      (pcomp 693 10 (mask 10) (dPK 3) (pcomp 693 10 (mask 10) (PS i)
        (pinvS 693 10 (mask 10) (dPK 3))))

theorem kNO1 : (normByK 5 3 CS.S CS.LR CS.TRI CS.BP && normByK 2 1 CX1.S CX1.LR CX1.TRI CX1.BP &&
    normByK 2 1 CX2.S CX2.LR CX2.TRI CX2.BP && normByK 1 1 CX3.S CX3.LR CX3.TRI CX3.BP &&
    normByK 5 3 CK1.S CK1.LR CK1.TRI CK1.BP && normByK 6 3 CK2.S CK2.LR CK2.TRI CK2.BP &&
    normByK 9 1 CA1.S CA1.LR CA1.TRI CA1.BP) = true := by
  decide +kernel

theorem kNO2 : (normByK 9 3 CA2.S CA2.LR CA2.TRI CA2.BP &&
    normByK 14 4 CK1A1.S CK1A1.LR CK1A1.TRI CK1A1.BP &&
    normByK 15 3 CK2A2.S CK2A2.LR CK2A2.TRI CK2A2.BP) = true := by
  decide +kernel

theorem kNO3 : (normByK 6 3 CSJ.S CSJ.LR CSJ.TRI CSJ.BP && normByK 12 2 CA3.S CA3.LR CA3.TRI CA3.BP &&
    normByK 4 2 CA4.S CA4.LR CA4.TRI CA4.BP && normByK 2 1 CX8.S CX8.LR CX8.TRI CX8.BP &&
    normByK 2 1 CSig.S CSig.LR CSig.TRI CSig.BP && normByK 3 3 CLam.S CLam.LR CLam.TRI CLam.BP &&
    normByK 3 1 CZ2S.S CZ2S.LR CZ2S.TRI CZ2S.BP && normByK 1 1 CZ.S CZ.LR CZ.TRI CZ.BP &&
    normByK 5 1 CX1Z.S CX1Z.LR CX1Z.TRI CX1Z.BP && normByK 5 1 CX6Z.S CX6Z.LR CX6Z.TRI CX6Z.BP) =
    true := by
  decide +kernel

theorem kNO4 : normByK 17 3 CP2.S CP2.LR CP2.TRI CP2.BP = true := by decide +kernel

theorem kNL : normByK 8 5 CL.S CL.LR CL.TRI CL.BP = true := by decide +kernel

theorem kLetter : (dLetters.all (fun k => Nat.beq (pcomp 693 10 (mask 10) (dPK 1) (sec3G k))
      (pcomp 693 10 (mask 10) (sec3G k) (dPK 1))) &&
    sLetters.all (fun k => Nat.beq (pcomp 693 10 (mask 10) (dPK 3) (sec3G k))
      (pcomp 693 10 (mask 10) (sec3G k) (dPK 3))) &&
    sPairs.all fun k => Nat.beq (pcomp 693 10 (mask 10) (dPK 3) (pcomp 693 10 (mask 10)
      (sec3G (k + 1)) (pinvS 693 10 (mask 10) (dPK 3))))
      (pcomp 693 10 (mask 10) (sec3G k) (sec3G (k + 1)))) = true := by
  decide +kernel

theorem letter_k : letterCheck = true := by
  have hk := kLetter
  simp only [Bool.and_eq_true] at hk
  have hl : (∀ k ∈ dLetters, k < 18) ∧ (∀ k ∈ sLetters, k < 18) ∧ ∀ k ∈ sPairs, k + 1 < 18 := by
    decide
  have cd := dPK_canon 1 (by norm_num)
  have cs := dPK_canon 3 (by norm_num)
  unfold letterCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨List.all_eq_true.2 fun k hk' => ?_, List.all_eq_true.2 fun k hk' => ?_⟩,
    List.all_eq_true.2 fun k hk' => ?_⟩
  · have h18 := hl.1 k hk'
    rw [hdT, hG k h18, comp_unpack cd (hc k h18), comp_unpack (hc k h18) cd,
      eq_unpack (canon_comp cd (hc k h18)) (canon_comp (hc k h18) cd)]
    exact List.all_eq_true.1 hk.1.1 k hk'
  · have h18 := hl.2.1 k hk'
    rw [hsT, hG k h18, comp_unpack cs (hc k h18), comp_unpack (hc k h18) cs,
      eq_unpack (canon_comp cs (hc k h18)) (canon_comp (hc k h18) cs)]
    exact List.all_eq_true.1 hk.1.2 k hk'
  · have h18 := hl.2.2 k hk'
    have h18' : k < 18 := by omega
    rw [hsT, hG (k + 1) h18, hG k h18', conj_unpack (dPK_perm 3 (by norm_num)) (hc _ h18),
      comp_unpack (hc k h18') (hc _ h18), eq_unpack (conj_canon (hc _ h18)
        (dPK_perm 3 (by norm_num))) (canon_comp (hc k h18') (hc _ h18))]
    exact List.all_eq_true.1 hk.2 k hk'

end CertificateChecks.KernelU6.Sec3
