
module

public import Certificates.Kernel.SporSch.Ru.R2257
public import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines

theorem cId : canonK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11) = true := by quickRfl
theorem cZF : canonK 1920 11 (mask 11) (1920 * 11) RuF.ZF = true := by quickRfl
theorem cL7 : canonK 1920 11 (mask 11) (1920 * 11) (RuT1920.L 7) = true := by quickRfl
theorem cL9 : canonK 1920 11 (mask 11) (1920 * 11) (RuT1920.L 9) = true := by quickRfl
theorem cL10 : canonK 1920 11 (mask 11) (1920 * 11) (RuT1920.L 10) = true := by quickRfl

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem sf_eq {j : Nat} (hj : j < 7) : ruSF j = unpack 1920 11 (RuT1920.L (7 + j)) := by
  have h1 : (ruLines1920.getD 1 (0, 0)).1 = 7 := rfl
  have h2 : (ruLines1920.getD 1 (0, 0)).2 = 7 := rfl
  rw [ruSF, RuR.field_get (f := 1) (by omega)]
  exact row1920 (by omega)

theorem pow_eq {p e : Nat} (hc : canonK 1920 11 (mask 11) (1920 * 11) p = true) :
    powA 1920 (unpack 1920 11 p) e = unpack 1920 11 (ppow 1920 11 (mask 11) (pidn 1920 11) p e) :=
  powEqRK_sound (by rw [powEqRK, hc]; exact Nat.beq_refl _)

theorem tv_eq {v : Nat} (hv : v < 8) : ruTv v = unpack 1920 11 (TV v) := by
  have h := TC.all v hv
  unfold tvok at h
  rw [strictB_eq', strictB_eq', strictB_eq'] at h
  obtain ⟨hA, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hB, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hC, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hAB, h⟩ := (bAnd_iff _ _).1 h
  have sf0 : ruSF 0 = unpack 1920 11 (RuT1920.L 7) := sf_eq (j := 0) (by omega)
  have sf2 : ruSF 2 = unpack 1920 11 (RuT1920.L 9) := sf_eq (j := 2) (by omega)
  have sf3 : ruSF 3 = unpack 1920 11 (RuT1920.L 10) := sf_eq (j := 3) (by omega)
  rw [ruTv, sf0, sf2, sf3, pow_eq cL7, pow_eq cL9,
    pow_eq cL10, compA_unpack hA hB, compA_unpack hAB hC, ← Nat.eq_of_beq_eq_true h]

theorem idA_eq : idA 1920 = unpack 1920 11 (pidn 1920 11) := (idK_sound idOK1920).symm

theorem zfK_eq {Y : Nat} (hY : canonK 1920 11 (mask 11) (1920 * 11) Y = true) :
    zfK Y = ruIsZF (unpack 1920 11 Y) := by
  rw [ruIsZF, idA_eq, RuF.zf_eq, canon_eqA hY cId, canon_eqA hY cZF, zfK]
  cases Nat.beq Y (pidn 1920 11) <;> rfl

theorem ord8K_eq {v : Nat} (hv : v < 8) {G : Nat} (hG : canonK 1920 11 (mask 11) (1920 * 11) G = true) :
    ord8K v G = ruOrd8F (compA 1920 (ruTv v) (unpack 1920 11 G)) := by
  have hT : canonK 1920 11 (mask 11) (1920 * 11) (TV v) = true := by
    have h := TC.all v hv
    unfold tvok at h
    rw [strictB_eq', strictB_eq', strictB_eq'] at h
    obtain ⟨_, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨_, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hC, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hAB, h⟩ := (bAnd_iff _ _).1 h
    rw [← Nat.eq_of_beq_eq_true h]
    exact canonK_pcomp hAB hC
  have cX := canonK_pcomp hT hG
  have cX2 := canonK_pcomp cX cX
  have cX4 := canonK_pcomp cX2 cX2
  have cX8 := canonK_pcomp cX4 cX4
  rw [tv_eq hv, compA_unpack hT hG]
  simp only [ord8K, strictB_eq', ruOrd8F]
  rw [compA_unpack cX cX, compA_unpack cX2 cX2, compA_unpack cX4 cX4, zfK_eq cX8, zfK_eq cX4]
  rfl

theorem rows4 : ∀ a < rcnt (RuRS.LR 0),
    row2K 1920 11 (mask 11) (1920 * 11) RuRS.LR RuRS.TR (ord8K 4) a = true := by
  intro a ha
  have hb : a < 256 := by
    have e := Nat.eq_of_beq_eq_true cnt0
    omega
  exact R4.all a hb

theorem bad_row {v : Nat} (hv : v < 8) (h4 : v ≠ 4) : BAD v < rcnt (RuRS.LR 0) ∧
    row2K 1920 11 (mask 11) (1920 * 11) RuRS.LR RuRS.TR (ord8K v) (BAD v) = false := by
  have hb := BC.all v hv
  unfold bad at hb
  have e : Nat.beq v 4 = false := by
    cases hb' : Nat.beq v 4
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb') h4
  rw [e, strictB_eq'] at hb
  obtain ⟨ha, hr⟩ := (bAnd_iff _ _).1 hb
  refine ⟨by simpa [Nat.blt_eq] using ha, ?_⟩
  cases e2 : row2K 1920 11 (mask 11) (1920 * 11) RuRS.LR RuRS.TR (ord8K v) (BAD v)
  · rfl
  · rw [e2] at hr
    exact absurd hr (by decide)

theorem all2_v {v : Nat} (hv : v < 8) :
    all2 1920 (rawLevels 1920 (ruField1920 4) (ruBaseArr 1920 ruRBase))
      (fun g => ruOrd8F (compA 1920 (ruTv v) g)) = (v == 4) := by
  have hpK : ∀ G, canonK 1920 11 (mask 11) (1920 * 11) G = true →
      ord8K v G = (fun g => ruOrd8F (compA 1920 (ruTv v) g)) (unpack 1920 11 G) :=
    fun G hG => ord8K_eq hv hG
  by_cases h4 : v = 4
  · subst h4
    have h := all2_of_rows (p := fun g => ruOrd8F (compA 1920 (ruTv 4) g)) (pK := ord8K 4) (LR := RuRS.LR) (TR := RuRS.TR) RuR.bindsR RuR.permR
      RuRS.hl (Nat.le_refl 2) hpK rows4
    rw [h]
    rfl
  · obtain ⟨ha, hr⟩ := bad_row hv h4
    have h := all2_false_of_row (p := fun g => ruOrd8F (compA 1920 (ruTv v) g)) (pK := ord8K v) (LR := RuRS.LR) (TR := RuRS.TR) RuR.bindsR
      RuR.permR RuRS.hl (Nat.le_refl 2) hpK ha hr
    rw [h]
    simp [h4]

theorem facts : ((List.range 8).map fun v => all2 1920 (rawLevels 1920 (ruField1920 4)
    (ruBaseArr 1920 ruRBase)) (fun g => ruOrd8F (compA 1920 (ruTv v) g))) =
    [false, false, false, false, true, false, false, false] := by
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.map_cons, List.map_nil, all2_v (by omega : (0 : Nat) < 8),
    all2_v (by omega : (1 : Nat) < 8), all2_v (by omega : (2 : Nat) < 8),
    all2_v (by omega : (3 : Nat) < 8), all2_v (by omega : (4 : Nat) < 8),
    all2_v (by omega : (5 : Nat) < 8), all2_v (by omega : (6 : Nat) < 8),
    all2_v (by omega : (7 : Nat) < 8)]
  all_goals rfl

end CertificateChecks.KernelSporSch.RuP

end
