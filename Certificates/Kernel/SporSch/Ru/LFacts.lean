module

public import Certificates.Kernel.SporSch.Ru.LChain
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.RuL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.RuSchreier CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines

theorem field_get {j : Nat} (hj : j < 6) : (ruField4060 5)[j]! = ruArr4060 (39 + j) := by
  rw [ruField4060, getElem!_pos _ j (by simpa [ruLines4060] using hj), Array.getElem_ofFn]
  rfl

theorem binds : Binds 4060 12 RuLS.S 6 2 RuLS.BP (ruField4060 5) (ruBaseArr 4060 ruLChainBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [ruField4060, ruLines4060],
    fun j hj => by
      have e : RuLS.S j = RuT4060.L (39 + j) := Nat.eq_of_beq_eq_true (allN_spec sOK j hj)
      rw [field_get hj, e]
      exact row4060 (by omega),
    by simp [ruBaseArr, ruLChainBase], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOK t ht)⟩

theorem chain : ruChainOK 4060 (ruField4060 5) 3 6 ruLChainBase ruLChainDerivations = true :=
  rawChainK_sound (CH := 2) (NS := RuLS.NS) binds RuLS.head RuLS.hl (by decide) RuLS.hs

theorem orbits : rawOrbitSizes 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase) = [1820, 64] := by
  rw [rawOrbitSizesK_sound binds perm RuLS.hl]
  simp [List.range_succ, Nat.eq_of_beq_eq_true cnt0, Nat.eq_of_beq_eq_true cnt1]

end CertificateChecks.KernelSporSch.RuL

end
