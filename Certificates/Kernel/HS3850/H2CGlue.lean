module

public import Certificates.Kernel.HS3850.H2CChecks
public import Certificates.Kernel.HS3850.Facts25371
public import CFSG.Certificates.Kernel.Spor.MulHTSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHS3850.H2C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.HN
open CFSG.KD.LQT.C4126 CFSG.KS.MulH CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.HarrisLit.N36.HS2C

theorem hc_eq {k : Nat} (hk : k < 43) : hsCentTbl k = tabT (unpack 3850 12 (HC.F k)) := by
  rw [← (CFSG.KD.HS3850.cent_parts hk).1, tabT_natArr]

theorem cHC {k : Nat} (hk : k < 43) : Cn (HC.F k) := (CFSG.KD.HS3850.cent_parts hk).2

theorem small' : permK G7 = true ∧ permK G5 = true ∧ permK X7 = true ∧ permK X5 = true ∧
    HC.F 28 = wfoldR ls8 SW7 ∧ HC.F 26 = wfoldR ls8 SW5 ∧
    Nat.beq (pc (HC.F 28) (HC.F 21)) (pc (HC.F 21) (HC.F 28)) = true ∧
    Nat.beq (pc (HC.F 26) (HC.F 21)) (pc (HC.F 21) (HC.F 26)) = true ∧
    Nat.beq (pw 7 (HC.F 28)) idn = true ∧ Nat.beq (pw 5 (HC.F 26)) idn = true ∧
    Nat.beq (pw 7 Z5) idn = true ∧ Nat.beq Z5 idn = false ∧
    Nat.beq (pw 5 W7) idn = true ∧ Nat.beq W7 idn = false := by
  have h := small
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ :=
    h
  exact ⟨h1, h2, h3, h4, (Nat.eq_of_beq_eq_true h5).symm, (Nat.eq_of_beq_eq_true h6).symm, h7, h8,
    h9, h10, h11, h12, h13, h14⟩

theorem permK_spec {P : Nat} (h : permK P = true) : Cn P ∧ Cn (pinv P) ∧
    invEqK 3850 12 (mask 12) (3850 * 12) P (pinv P) = true := by
  unfold permK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem pw_unpack {P : Nat} (hP : Cn P) : ∀ e,
    powT 3850 e (tabT (unpack 3850 12 P)) = tabT (unpack 3850 12 (pw e P)) ∧ Cn (pw e P)
  | 0 => by
    refine ⟨?_, cIdn⟩
    change idT 3850 = tabT (unpack 3850 12 idn)
    rw [idT_tabT, CFSG.KC.BfsPin.idA_eq (w := 12) (by decide)]
    rfl
  | e + 1 => by
    obtain ⟨h1, h2⟩ := pw_unpack hP e
    refine ⟨?_, CFSG.KD.HS3850.cn_pc hP h2⟩
    change compT 3850 (tabT (unpack 3850 12 P)) (powT 3850 e (tabT (unpack 3850 12 P))) =
      tabT (unpack 3850 12 (pc P (pw e P)))
    rw [h1, compT_unpack hP h2]
    rfl

theorem idT_eq : idT 3850 = tabT (unpack 3850 12 idn) := by
  rw [idT_tabT, CFSG.KC.BfsPin.idA_eq (w := 12) (by decide)]
  rfl

theorem hs2CCheck_true : hs2CCheck = true := by
  obtain ⟨kG7, kG5, kX7, kX5, w7, w5, c7, c5, o7, o5, z7, z1, u5, u1⟩ := small'
  obtain ⟨cG7, cG7i, iG7⟩ := permK_spec kG7
  obtain ⟨cG5, cG5i, iG5⟩ := permK_spec kG5
  obtain ⟨cX7, cX7i, iX7⟩ := permK_spec kX7
  obtain ⟨cX5, cX5i, iX5⟩ := permK_spec kX5
  have c21 := cHC (k := 21) (by norm_num)
  have c23 := cHC (k := 23) (by norm_num)
  have c24 := cHC (k := 24) (by norm_num)
  have c25 := cHC (k := 25) (by norm_num)
  have c26 := cHC (k := 26) (by norm_num)
  have c28 := cHC (k := 28) (by norm_num)
  have et : t2C = tabT (unpack 3850 12 (HC.F 21)) := hc_eq (by norm_num)
  have ey7 : y7 = tabT (unpack 3850 12 (HC.F 28)) := hc_eq (by norm_num)
  have ey5 : y5 = tabT (unpack 3850 12 (HC.F 26)) := hc_eq (by norm_num)
  have eg7 : g7 = tabT (unpack 3850 12 G7) := by
    unfold g7
    rw [hc_eq (k := 23) (by norm_num), hc_eq (k := 24) (by norm_num), compT_unpack c23 c24]
    rfl
  have eg5 : g5 = tabT (unpack 3850 12 G5) := by
    unfold g5
    rw [hc_eq (k := 25) (by norm_num), hc_eq (k := 23) (by norm_num), compT_unpack c25 c23]
    rfl
  have eig7 : invT 3850 g7 = tabT (unpack 3850 12 (pinv G7)) := by
    rw [eg7, invT_unpack (by norm_num) iG7]
  have eig5 : invT 3850 g5 = tabT (unpack 3850 12 (pinv G5)) := by
    rw [eg5, invT_unpack (by norm_num) iG5]
  have ex7 : x7 = tabT (unpack 3850 12 X7) := by
    unfold x7
    rw [eig7, eg7, ey7, compT_unpack cG7 c28,
      compT_unpack (p := pcomp 3850 12 (mask 12) G7 (HC.F 28)) (CFSG.KD.HS3850.cn_pc cG7 c28) cG7i]
    rfl
  have ex5 : x5 = tabT (unpack 3850 12 X5) := by
    unfold x5
    rw [eig5, eg5, ey5, compT_unpack cG5 c26,
      compT_unpack (p := pcomp 3850 12 (mask 12) G5 (HC.F 26)) (CFSG.KD.HS3850.cn_pc cG5 c26) cG5i]
    rfl
  have p21 : permOK 3850 t2C = true := CFSG.KD.LQT.HN.cent_perm (k := 21) (by norm_num) c21
  have p23 : permOK 3850 (hsCentTbl 23) = true := CFSG.KD.LQT.HN.cent_perm (by norm_num) c23
  have p24 : permOK 3850 (hsCentTbl 24) = true := CFSG.KD.LQT.HN.cent_perm (by norm_num) c24
  have p25 : permOK 3850 (hsCentTbl 25) = true := CFSG.KD.LQT.HN.cent_perm (by norm_num) c25
  have py7 : permOK 3850 y7 = true := CFSG.KD.LQT.HN.cent_perm (k := 28) (by norm_num) c28
  have py5 : permOK 3850 y5 = true := CFSG.KD.LQT.HN.cent_perm (k := 26) (by norm_num) c26
  have pg7 : permOK 3850 g7 = true := by rw [eg7]; exact permOK_unpack cG7 iG7
  have pg5 : permOK 3850 g5 = true := by rw [eg5]; exact permOK_unpack cG5 iG5
  have px7 : permOK 3850 x7 = true := by rw [ex7]; exact permOK_unpack cX7 iX7
  have px5 : permOK 3850 x5 = true := by rw [ex5]; exact permOK_unpack cX5 iX5
  have s7 : hsSift y7 = true :=
    CFSG.KD.HS3850.sift_true_of_word (by decide) (CFSG.KD.HS3850.cent_parts (k := 28) (by norm_num)).1
      w7
  have s5 : hsSift y5 = true :=
    CFSG.KD.HS3850.sift_true_of_word (by decide) (CFSG.KD.HS3850.cent_parts (k := 26) (by norm_num)).1
      w5
  have cm7 : commTT 3850 y7 t2C = true := by rw [ey7, et, commTT_unpack c28 c21]; exact c7
  have cm5 : commTT 3850 y5 t2C = true := by rw [ey5, et, commTT_unpack c26 c21]; exact c5
  have q7 : tblEq 3850 (powT 3850 7 y7) (idT 3850) = true := by
    rw [ey7, (pw_unpack c28 7).1, idT_eq, tblEq_unpack (pw_unpack c28 7).2 cIdn]
    exact o7
  have q5 : tblEq 3850 (powT 3850 5 y5) (idT 3850) = true := by
    rw [ey5, (pw_unpack c26 5).1, idT_eq, tblEq_unpack (pw_unpack c26 5).2 cIdn]
    exact o5
  have v7 : invOK 3850 g7 (invT 3850 g7) = true := by
    rw [eig7, eg7]
    exact invOK_unpack cG7 cG7i iG7
  have v5 : invOK 3850 g5 (invT 3850 g5) = true := by
    rw [eig5, eg5]
    exact invOK_unpack cG5 cG5i iG5
  have cZ7 : Cn Z7 := CFSG.KD.HS3850.cn_pc c28 cX7
  have ez7 : compT 3850 y7 x7 = tabT (unpack 3850 12 Z7) := by
    rw [ey7, ex7, compT_unpack c28 cX7]
    rfl
  have cW7 : Cn W7 := (pw_unpack cZ7 3).2
  have ew7 : powT 3850 3 (compT 3850 y7 x7) = tabT (unpack 3850 12 W7) := by
    rw [ez7]
    exact (pw_unpack cZ7 3).1
  have r5 : tblEq 3850 (powT 3850 5 (powT 3850 3 (compT 3850 y7 x7))) (idT 3850) = true := by
    rw [ew7, (pw_unpack cW7 5).1, idT_eq, tblEq_unpack (pw_unpack cW7 5).2 cIdn]
    exact u5
  have r3 : tblEq 3850 (powT 3850 3 (compT 3850 y7 x7)) (idT 3850) = false := by
    rw [ew7, idT_eq, tblEq_unpack cW7 cIdn]
    exact u1
  have cZ5 : Cn Z5 := CFSG.KD.HS3850.cn_pc c26 cX5
  have ez5 : compT 3850 y5 x5 = tabT (unpack 3850 12 Z5) := by
    rw [ey5, ex5, compT_unpack c26 cX5]
    rfl
  have r7 : tblEq 3850 (powT 3850 7 (compT 3850 y5 x5)) (idT 3850) = true := by
    rw [ez5, (pw_unpack cZ5 7).1, idT_eq, tblEq_unpack (pw_unpack cZ5 7).2 cIdn]
    exact z7
  have r1 : tblEq 3850 (compT 3850 y5 x5) (idT 3850) = false := by
    rw [ez5, idT_eq, tblEq_unpack cZ5 cIdn]
    exact z1
  unfold hs2CCheck
  rw [p21, p23, p24, p25, py7, s7, cm7, q7, py5, s5, cm5, q5, pg7, v7, pg5, v5, px7, r5, r3, px5,
    r7, r1]
  rfl

end CertificateChecks.KernelHS3850.H2C

end
