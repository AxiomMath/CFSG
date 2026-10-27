module

public import Certificates.Kernel.SporSch.Tits.Central2263
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsTitsFactsInputs
meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsTitsFactsInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelSporSch.TitsP.J0 11 CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.aJ0
#ks_perm CertificateChecks.KernelSporSch.TitsP.J1 11 CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.aJ1
#ks_perm CertificateChecks.KernelSporSch.TitsP.J2 11 CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.aJ2
#ks_perm CertificateChecks.KernelSporSch.TitsP.K0 11 CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.aK0
#ks_perm CertificateChecks.KernelSporSch.TitsP.Jy 11 CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.aJy
#ks_perm CertificateChecks.KernelSporSch.TitsP.Ky1 11
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.aKy1
#ks_perm CertificateChecks.KernelSporSch.TitsP.Ky2 11
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.aKy2
#ks_perm CertificateChecks.KernelSporSch.TitsP.Ky3 11
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.aKy3
#ks_perm CertificateChecks.KernelSporSch.TitsP.Jc 11 CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.aJc
#ks_perm CertificateChecks.KernelSporSch.TitsP.Kc1 11
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.aKc1
#ks_perm CertificateChecks.KernelSporSch.TitsP.Kc2 11
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.aKc2
#ks_perm CertificateChecks.KernelSporSch.TitsP.Kc3 11
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.aKc3

namespace CertificateChecks.KernelSporSch.TitsPairs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsCentral

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 1755 11 (mask 11) p

@[expose] noncomputable def okI (p : Nat) : Bool :=
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) p, bAnd(canonK 1755 11 (mask 11) (1755 * 11) (pinv p),
    permOK 1755 11 (mask 11) (1755 * 11) p (pinv p)))

@[expose] noncomputable def wE (wd : List Int) (r : Nat) : Bool :=
  wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13 wd r

theorem cc {p q : Nat} (hp : C p) (hq : C q) : C (pc p q) := canonK_pcomp hp hq

theorem cu {p q : Nat} (hp : C p) (hq : C q) :
    compA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = unpack 1755 11 (pc p q) :=
  compA_unpack hp hq

theorem okI_spec {p : Nat} (h : okI p = true) :
    C p ∧ C (pinv p) ∧ invCand 1755 (unpack 1755 11 p) = unpack 1755 11 (pinv p) ∧
      isInvA 1755 (unpack 1755 11 p) (invCand 1755 (unpack 1755 11 p)) = true := by
  unfold okI at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  exact ⟨h1, h2, (invEqK_sound h3).1, isInv_of h3⟩

theorem wE_spec {wd : List Int} {r : Nat} (h : wE wd r = true) :
    wordArr 1755 titsDerivedArrs wd = unpack 1755 11 r :=
  (wordEqK_sound ⟨bindsD.2.2.2.1, bindsD.2.2.2.2.1⟩ permD h).1

theorem or2 {a b : Bool} (h : bIf(a, true, b) = true) : (a || b) = true := by
  revert h
  cases a <;> cases b <;> decide

theorem or4 {a b c d : Bool} (h : bIf(a, true, bIf(b, true, bIf(c, true, d))) = true) :
    (a || b || c || d) = true := by
  revert h
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem wJ0 : wE [-4, -4] TitsP.J0 = true := by
  unfold wE wordEqK
  quickRfl
theorem wJ1 : wE [-4, 3, 3] TitsP.J1 = true := by
  unfold wE wordEqK
  quickRfl
theorem wJ2 : wE [3, 4, 3] TitsP.J2 = true := by
  unfold wE wordEqK
  quickRfl
theorem wK0 : wE [13] TitsP.K0 = true := by
  unfold wE wordEqK
  quickRfl

theorem j0_eq : aJ0 = unpack 1755 11 TitsP.J0 := wE_spec wJ0
theorem j1_eq : aJ1 = unpack 1755 11 TitsP.J1 := wE_spec wJ1
theorem j2_eq : aJ2 = unpack 1755 11 TitsP.J2 := wE_spec wJ2
theorem k0_eq : aK0 = unpack 1755 11 TitsP.K0 := wE_spec wK0

theorem oJ0 : okI TitsP.J0 = true := by quickRfl
theorem oJ1 : okI TitsP.J1 = true := by quickRfl
theorem oJ2 : okI TitsP.J2 = true := by quickRfl
theorem oK0 : okI TitsP.K0 = true := by quickRfl
theorem oJy : okI TitsP.Jy = true := by quickRfl
theorem oKy1 : okI TitsP.Ky1 = true := by quickRfl
theorem oKy2 : okI TitsP.Ky2 = true := by quickRfl
theorem oKy3 : okI TitsP.Ky3 = true := by quickRfl
theorem cJc : C TitsP.Jc := by quickRfl
theorem cKc1 : C TitsP.Kc1 := by quickRfl
theorem cKc2 : C TitsP.Kc2 := by quickRfl
theorem cKc3 : C TitsP.Kc3 := by quickRfl

theorem eJy : Nat.beq (pc (pc TitsP.J2 TitsP.J0) TitsP.J2) TitsP.Jy = true := by quickRfl
theorem eKy1 : Nat.beq (pc (pc (pc TitsP.J0 TitsP.K0) TitsP.K0) (pinv TitsP.J0)) TitsP.Ky1 = true := by
  quickRfl
theorem eKy2 : Nat.beq (pc (pc (pc (pinv TitsP.J0) TitsP.K0) TitsP.K0) TitsP.J0) TitsP.Ky2 = true := by
  quickRfl
theorem eKy3 : Nat.beq (pc (pc (pc (pc (pc TitsP.J0 TitsP.J0) TitsP.K0) TitsP.K0) TitsP.J0) TitsP.J0)
    TitsP.Ky3 = true := by quickRfl
theorem eJc : Nat.beq (pc (pc (pc (pinv TitsP.J0) (pinv TitsP.Jy)) TitsP.J0) TitsP.Jy) TitsP.Jc =
    true := by quickRfl
theorem eKc1 : Nat.beq (pc (pc (pc (pinv TitsP.K0) (pinv TitsP.Ky1)) TitsP.K0) TitsP.Ky1)
    TitsP.Kc1 = true := by quickRfl
theorem eKc2 : Nat.beq (pc (pc (pc (pinv TitsP.K0) (pinv TitsP.Ky2)) TitsP.K0) TitsP.Ky2)
    TitsP.Kc2 = true := by quickRfl
theorem eKc3 : Nat.beq (pc (pc (pc (pinv TitsP.K0) (pinv TitsP.Ky3)) TitsP.K0) TitsP.Ky3)
    TitsP.Kc3 = true := by quickRfl

theorem jy_eq : aJy = unpack 1755 11 TitsP.Jy := by
  have a := (okI_spec oJ0).1
  have b := (okI_spec oJ2).1
  unfold aJy
  rw [j2_eq, j0_eq, cu b a, cu (cc b a) b, Nat.eq_of_beq_eq_true eJy]

theorem ky1_eq : aKy1 = unpack 1755 11 TitsP.Ky1 := by
  obtain ⟨a, ai, ia, -⟩ := okI_spec oJ0
  have k := (okI_spec oK0).1
  unfold aKy1
  rw [j0_eq, k0_eq, ia, cu a k, cu (cc a k) k, cu (cc (cc a k) k) ai, Nat.eq_of_beq_eq_true eKy1]

theorem ky2_eq : aKy2 = unpack 1755 11 TitsP.Ky2 := by
  obtain ⟨a, ai, ia, -⟩ := okI_spec oJ0
  have k := (okI_spec oK0).1
  unfold aKy2
  rw [j0_eq, k0_eq, ia, cu ai k, cu (cc ai k) k, cu (cc (cc ai k) k) a, Nat.eq_of_beq_eq_true eKy2]

theorem ky3_eq : aKy3 = unpack 1755 11 TitsP.Ky3 := by
  have a := (okI_spec oJ0).1
  have k := (okI_spec oK0).1
  unfold aKy3
  rw [j0_eq, k0_eq, cu a a, cu (cc a a) k, cu (cc (cc a a) k) k, cu (cc (cc (cc a a) k) k) a,
    cu (cc (cc (cc (cc a a) k) k) a) a, Nat.eq_of_beq_eq_true eKy3]

theorem comm_of {x y r : Nat} {X Y : Array Nat} (hX : X = unpack 1755 11 x)
    (hY : Y = unpack 1755 11 y) (ox : okI x = true) (oy : okI y = true)
    (h : Nat.beq (pc (pc (pc (pinv x) (pinv y)) x) y) r = true) :
    commArr 1755 X Y = unpack 1755 11 r := by
  obtain ⟨a, ai, ia, -⟩ := okI_spec ox
  obtain ⟨b, bi, ib, -⟩ := okI_spec oy
  unfold commArr
  rw [hX, hY, ia, ib, cu ai bi, cu (cc ai bi) a, cu (cc (cc ai bi) a) b, Nat.eq_of_beq_eq_true h]

theorem jc_eq : aJc = unpack 1755 11 TitsP.Jc := comm_of j0_eq jy_eq oJ0 oJy eJc
theorem kc1_eq : aKc1 = unpack 1755 11 TitsP.Kc1 := comm_of k0_eq ky1_eq oK0 oKy1 eKc1
theorem kc2_eq : aKc2 = unpack 1755 11 TitsP.Kc2 := comm_of k0_eq ky2_eq oK0 oKy2 eKc2
theorem kc3_eq : aKc3 = unpack 1755 11 TitsP.Kc3 := comm_of k0_eq ky3_eq oK0 oKy3 eKc3

theorem n01 : neK 1755 11 (mask 11) (1755 * 11) (pc TitsP.J0 TitsP.J1) (pc TitsP.J1 TitsP.J0) =
    true := by quickRfl
theorem n00 : neK 1755 11 (mask 11) (1755 * 11) (pc TitsP.K0 TitsP.J0) (pc TitsP.J0 TitsP.K0) =
    true := by quickRfl

theorem sHJ : allL (fun c => bIf(Nat.beq c (pidn 1755 11), true, Nat.beq c TitsP.Jc)) TitsCHJ.L =
    true := by quickRfl
theorem sNK : allL (fun c => bIf(Nat.beq c (pidn 1755 11), true, bIf(Nat.beq c TitsP.Kc1, true,
    bIf(Nat.beq c TitsP.Kc2, true, Nat.beq c TitsP.Kc3)))) TitsCNK.L = true := by quickRfl

theorem facts :
    isInvA 1755 aJ0 (invCand 1755 aJ0) = true ∧ isInvA 1755 aJ1 (invCand 1755 aJ1) = true ∧
      isInvA 1755 aJ2 (invCand 1755 aJ2) = true ∧ isInvA 1755 aK0 (invCand 1755 aK0) = true ∧
      isInvA 1755 aJy (invCand 1755 aJy) = true ∧ isInvA 1755 aKy1 (invCand 1755 aKy1) = true ∧
      isInvA 1755 aKy2 (invCand 1755 aKy2) = true ∧ isInvA 1755 aKy3 (invCand 1755 aKy3) = true ∧
      eqA 1755 (compA 1755 aJ0 aJ1) (compA 1755 aJ1 aJ0) = false ∧
      eqA 1755 (compA 1755 aK0 aJ0) (compA 1755 aJ0 aK0) = false ∧
      (titsCHJ.all fun c => eqA 1755 c (idA 1755) || eqA 1755 c aJc) = true ∧
      (titsCNK.all fun c => eqA 1755 c (idA 1755) || eqA 1755 c aKc1 || eqA 1755 c aKc2 ||
        eqA 1755 c aKc3) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [j0_eq]
    exact (okI_spec oJ0).2.2.2
  · rw [j1_eq]
    exact (okI_spec oJ1).2.2.2
  · rw [j2_eq]
    exact (okI_spec oJ2).2.2.2
  · rw [k0_eq]
    exact (okI_spec oK0).2.2.2
  · rw [jy_eq]
    exact (okI_spec oJy).2.2.2
  · rw [ky1_eq]
    exact (okI_spec oKy1).2.2.2
  · rw [ky2_eq]
    exact (okI_spec oKy2).2.2.2
  · rw [ky3_eq]
    exact (okI_spec oKy3).2.2.2
  · have a := (okI_spec oJ0).1
    have b := (okI_spec oJ1).1
    rw [j0_eq, j1_eq, cu a b, cu b a]
    exact neK_sound n01
  · have a := (okI_spec oK0).1
    have b := (okI_spec oJ0).1
    rw [k0_eq, j0_eq, cu a b, cu b a]
    exact neK_sound n00
  · rw [chj_eq, List.all_map, List.all_eq_true]
    intro c hc
    have h := canon_of_HJ hc
    change (eqA 1755 (unpack 1755 11 c) (idA 1755) || eqA 1755 (unpack 1755 11 c) aJc) = true
    rw [TitsCentral.id_eq, jc_eq, eqA_unpack h canId, eqA_unpack h cJc]
    exact or2 (allL_spec sHJ c hc)
  · rw [cnk_eq, List.all_map, List.all_eq_true]
    intro c hc
    have h := canon_of_NK hc
    change (eqA 1755 (unpack 1755 11 c) (idA 1755) || eqA 1755 (unpack 1755 11 c) aKc1 ||
      eqA 1755 (unpack 1755 11 c) aKc2 || eqA 1755 (unpack 1755 11 c) aKc3) = true
    rw [TitsCentral.id_eq, kc1_eq, kc2_eq, kc3_eq, eqA_unpack h canId, eqA_unpack h cKc1, eqA_unpack h cKc2,
      eqA_unpack h cKc3]
    exact or4 (allL_spec sNK c hc)

end CertificateChecks.KernelSporSch.TitsPairs

end
