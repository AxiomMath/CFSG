module

public import Certificates.Kernel.LyGlue.Hex
public import CFSG.Certificates.Kernel.LyGlue.HexSound
public import CFSG.Certificates.Kernel.HexArrsSound
public import CFSG.Sporadic.Recognition.LyonsModelPerm

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.HardMathSupport.Solomon.Coordinator

theorem hexCK_spec : ∀ {cs : List Char}, hexCK cs = true → ∀ c ∈ cs, IsLowHex c
  | [], _, c, hc => by cases hc
  | ch :: cs, h, c, hc => by
    change ((Nat.blt (Char.toNat ch) 58 && Nat.ble 48 (Char.toNat ch) ||
      Nat.blt (Char.toNat ch) 103 && Nat.ble 97 (Char.toNat ch)) && hexCK cs) = true at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · have h1 := h.1
      simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h1
      unfold IsLowHex
      omega
    · exact hexCK_spec h.2 c hc

theorem cLen : CH.chars.length = 5 * 66825 := by decide +kernel

theorem dLen : DH.chars.length = 5 * 66825 := by decide +kernel

theorem cT_get {a : Nat} (ha : a < 66825) : (Ly0.cT[a]!).toNat = cL a := by
  have e : Ly0.cT = Ly0.tabOfHex (String.ofList CH.chars) := by
    rw [← CH.eq]
    rfl
  rw [e, tabOfHex_get cLen (hexCK_spec cHex) ha,
    (CFSG.KC.HexArrs.hexArrs_sound CH.all).2 (a / 4455) (by rw [cN]; omega)]
  unfold unpack
  rw [getElem!_pos _ (a % 4455) (by simp; omega), Array.getElem_ofFn]
  change _ = pg 17 (mask 17) (CS (a / 4455)) (a % 4455)
  rw [cS_eq (show a / 4455 < 15 by omega)]

theorem dT_get {a : Nat} (ha : a < 66825) : (Ly0.dT[a]!).toNat = dL a := by
  have e : Ly0.dT = Ly0.tabOfHex (String.ofList DH.chars) := by
    rw [← DH.eq]
    rfl
  rw [e, tabOfHex_get dLen (hexCK_spec dHex) ha,
    (CFSG.KC.HexArrs.hexArrs_sound DH.all).2 (a / 4455) (by rw [dN]; omega)]
  unfold unpack
  rw [getElem!_pos _ (a % 4455) (by simp; omega), Array.getElem_ofFn]
  change _ = pg 17 (mask 17) (DS (a / 4455)) (a % 4455)
  rw [dS_eq (show a / 4455 < 15 by omega)]

theorem cL_eq (h : Ly0.tabCheck = true) (a : Fin Ly0.deg) : cL a = (Ly0.cG a : Nat) := by
  have := Ly0.rep_cG h a a.2
  rw [idx_of_lt _ a.2] at this
  rw [← cT_get a.2]
  exact this

theorem dL_eq (h : Ly0.tabCheck = true) (a : Fin Ly0.deg) : dL a = (Ly0.dG a : Nat) := by
  have := Ly0.rep_dG h a a.2
  rw [idx_of_lt _ a.2] at this
  rw [← dT_get a.2]
  exact this

end CertificateChecks.KernelLy

end
