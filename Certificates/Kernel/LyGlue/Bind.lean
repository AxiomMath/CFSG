module

public import Certificates.Kernel.LyGlue.Hex
public import CFSG.Sporadic.Recognition.LyonsModelPerm

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

theorem tabOfBlks_get (B : Array Nat) {a : Nat} (ha : a < 66825) :
    ((Ly0.tabOfBlks B)[a]!).toNat = pg 17 (mask 17) B[a / 4455]! (a % 4455) := by
  have hlt : ∀ x : Nat, Nat.land x 131071 < 2 ^ 32 :=
    fun x => Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  unfold Ly0.tabOfBlks
  rw [getElem!_pos _ a (by simp; omega), Array.getElem_ofFn, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (hlt _)]
  rfl

theorem cT_get {a : Nat} (ha : a < 66825) : (Ly0.cT[a]!).toNat = cL a := by
  unfold Ly0.cT
  rw [tabOfBlks_get _ ha, ← cS_eq (show a / 4455 < 15 by omega)]
  rfl

theorem dT_get {a : Nat} (ha : a < 66825) : (Ly0.dT[a]!).toNat = dL a := by
  unfold Ly0.dT
  rw [tabOfBlks_get _ ha, ← dS_eq (show a / 4455 < 15 by omega)]
  rfl

theorem cL_eq (h : Ly0.tabCheck = true) (a : Fin Ly0.deg) : cL a = (Ly0.cG a : Nat) := by
  have := Ly0.rep_cG h a a.2
  rw [idx_of_lt _ a.2, Equiv.Perm.smul_def, Fin.eta] at this
  unfold ap at this
  rw [← cT_get a.2]
  exact this

theorem dL_eq (h : Ly0.tabCheck = true) (a : Fin Ly0.deg) : dL a = (Ly0.dG a : Nat) := by
  have := Ly0.rep_dG h a a.2
  rw [idx_of_lt _ a.2, Equiv.Perm.smul_def, Fin.eta] at this
  unfold ap at this
  rw [← dT_get a.2]
  exact this

end CertificateChecks.KernelLy

end
