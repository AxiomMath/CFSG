module

public import Certificates.Kernel.HS3850.Fus
public import Certificates.Kernel.HS3850.Kit
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import Certificates.Data.FooteLitCF23HSCheck
public import Certificates.Kernel.LocalQT.HSAut.F4146

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KC.PkPow CFSG.KD.LQT.C4126
open CFSG.KS.MulH CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.GSThmB.CF23I.HS
open CFSG.KD.LQT.HO (Cn cIdn)
open CFSG.Monster.B.Co2.Native (idA)

theorem cent_tab {k : Nat} (hk : k < 43) : hsCentTbl k = tabT (unpack 3850 12 (HC.F k)) := by
  rw [← (cent_parts hk).1, tabT_natArr]

theorem cent_cn {k : Nat} (hk : k < 43) : Cn (HC.F k) := (cent_parts hk).2

theorem hidc : canonK 3850 12 (mask 12) (3850 * 12) (pidn 3850 12) = true := cIdn

theorem hidA : idA 3850 = unpack 3850 12 (pidn 3850 12) := CFSG.KC.BfsPin.idA_eq (by decide)

theorem hid : idT 3850 = tabT (unpack 3850 12 (pidn 3850 12)) := by rw [idT_tabT, hidA]

theorem compT_pc {p q : Nat} (hp : Cn p) (hq : Cn q) :
    compT 3850 (tabT (unpack 3850 12 p)) (tabT (unpack 3850 12 q)) = tabT (unpack 3850 12 (pc p q)) :=
  compT_unpack hp hq

theorem pows (X : Nat) : Pows 3850 12 X (pw X) :=
  ⟨rfl, fun e => CFSG.KS.Raw.Orb.strictN_eq _ _⟩

theorem cperm {k : Nat} (hk : k < 43) : CFSG.Sporadic.SmallOddCore.permOK 3850 (hsCentTbl k) = true :=
  CFSG.KD.LQT.HN.cent_perm hk (cent_cn hk)

theorem gens12_get {i : Nat} (hi : i < 6) :
    gens12.getD i (idT 3850) = hsCentTbl ([6, 7, 13, 14, 15, 16].getD i 0) := by
  interval_cases i <;> rfl

theorem g12_parts : ∀ l ∈ [1, 6, 1, 6, 2, 2], gens12.getD (l - 1) (idT 3850) =
    tabT (unpack 3850 12 (g12 l)) ∧ canonK 3850 12 (mask 12) (3850 * 12) (g12 l) = true := by
  intro l hl
  have h1 : l - 1 < 6 := by simp at hl; omega
  have h2 : [6, 7, 13, 14, 15, 16].getD (l - 1) 0 < 43 := by
    rcases l - 1 with _ | _ | _ | _ | _ | _ | i <;> simp
  rw [gens12_get h1]
  exact ⟨cent_tab h2, cent_cn h2⟩

theorem c0_eq : c0Tbl = tabT (unpack 3850 12 c0K) ∧ Cn c0K :=
  wordTbl_unpack hid hidc g12_parts

theorem g4_parts : ∀ l ∈ [1, 2, 3], gens4.getD (l - 1) (idT 3850) =
    tabT (unpack 3850 12 (g4 l)) ∧ canonK 3850 12 (mask 12) (3850 * 12) (g4 l) = true := by
  intro l hl
  have h1 : l - 1 < 4 := by simp at hl; omega
  have h2 : 34 + l < 43 := by simp at hl; omega
  have e : gens4.getD (l - 1) (idT 3850) = hsCentTbl (34 + l) := by
    simp at hl
    rcases hl with rfl | rfl | rfl <;> rfl
  rw [e]
  exact ⟨cent_tab h2, cent_cn h2⟩

theorem x_eq : xTbl = tabT (unpack 3850 12 xK) ∧ Cn xK :=
  wordTbl_unpack hid hidc fun l hl => g4_parts l (by simp at hl; simp [hl])

theorem y_eq : yTbl = tabT (unpack 3850 12 yK) ∧ Cn yK :=
  wordTbl_unpack hid hidc fun l hl => g4_parts l (by simp at hl; rcases hl with rfl | rfl <;> simp)

theorem d0_eq : d0Tbl = tabT (unpack 3850 12 d0K) ∧ Cn d0K := by
  have c13 := cent_cn (k := 13) (by norm_num)
  have c14 := cent_cn (k := 14) (by norm_num)
  unfold d0Tbl d0K
  rw [cent_tab (k := 13) (by norm_num), cent_tab (k := 14) (by norm_num), compT_pc c13 c13,
    compT_pc (cn_pc c13 c13) c14, compT_pc (cn_pc (cn_pc c13 c13) c14) c13]
  exact ⟨rfl, cn_pc (cn_pc (cn_pc c13 c13) c14) c13⟩

theorem ord_of {X m : Nat} (hX : Cn X) (h : ordK X m = true) :
    CFSG.Sporadic.Schreier.Native.ordTest 3850 m (tabT (unpack 3850 12 X)) = true := by
  rw [ordTest_unpack (pows X) hidA hidc hX]
  unfold ordK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [Bool.and_eq_true]
  exact ⟨h1, h2⟩

theorem hsFusOK_true : hsFusOK = true := by
  have h := ok23203
  rw [CFSG.KS.PEnum.strictB_app'] at h
  simp only [bAnd_iff] at h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := h
  obtain ⟨hc, cc⟩ := c0_eq
  obtain ⟨hd, cd⟩ := d0_eq
  obtain ⟨hx, cx⟩ := x_eq
  obtain ⟨hy, cy⟩ := y_eq
  have c12 := cent_cn (k := 12) (by norm_num)
  have hinv := invT_unpack (by norm_num) f4
  unfold hsFusOK
  rw [hc, hd, hx, hy, hinv, cent_tab (k := 12) (by norm_num), compT_pc f3 c12,
    compT_pc (cn_pc f3 c12) cc, compT_pc c12 cd, compT_pc cx cy,
    tblEq_unpack (cn_pc (cn_pc f3 c12) cc) (cn_pc c12 cd), involOK_unpack' (by norm_num) hid hidc cd,
    invOK_unpack cc f3 f4, ord_of cx f6, ord_of cy f7, ord_of (cn_pc cx cy) f8, ← cent_tab (k := 12)
    (by norm_num), cperm (k := 12) (by norm_num)]
  simp only [gens12, gens4, List.all_cons, List.all_nil, cperm (by norm_num : 6 < 43),
    cperm (by norm_num : 7 < 43), cperm (by norm_num : 13 < 43), cperm (by norm_num : 14 < 43),
    cperm (by norm_num : 15 < 43), cperm (by norm_num : 16 < 43), cperm (by norm_num : 35 < 43),
    cperm (by norm_num : 36 < 43), cperm (by norm_num : 37 < 43), cperm (by norm_num : 38 < 43),
    Bool.and_true, Bool.true_and]
  have e1 : pcomp 3850 12 (mask 12) d0K d0K = pidn 3850 12 := Nat.eq_of_beq_eq_true f1
  have e2 : Nat.beq d0K (pidn 3850 12) = false := by
    have h := f2
    simp only [Bool.not_eq_true'] at h
    exact h
  rw [e1, e2, Nat.eq_of_beq_eq_true f5, Nat.beq_refl, Nat.beq_refl]
  rfl

end CFSG.KD.HS3850

end
