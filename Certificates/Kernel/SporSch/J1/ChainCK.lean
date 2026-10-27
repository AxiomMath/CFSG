module

public import Certificates.Kernel.SporSch.J1.Levels
public import Certificates.Kernel.SporSch.J1.Chain2165
public import CFSG.Certificates.Kernel.SporSch.ChainCKDefs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawCard
public import CFSG.Sporadic.Schreier.J1CountCheckInputs
public import Certificates.Data.Kernel.SporSch.J1Pt

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Mathieu CFSG.Certificates.Native

theorem bindsL : allN 4 (fun k =>
    bindListK 3080 12 (J1L.S k) (j1Chain.strongGenerators.getD k [])) = true := by
  quickRfl

theorem baseL : allN 3 (fun t => Nat.beq j1Chain.baseArr[t]! (pg 12 (mask 12) J1L.BP t)) =
    true := by
  quickRfl

theorem bindA : bindListK 3080 12 (J1L.S 0) (j1Chain.generators.getD 0 []) = true := by quickRfl

theorem bindB : bindListK 3080 12 (J1L.S 1) (j1Chain.generators.getD 1 []) = true := by quickRfl

theorem strong_eqL (j : Nat) (hj : j < 4) : j1Chain.strongArrs[j]! = unpack 3080 12 (J1L.S j) := by
  have h := toArray_eq_of_bindListK (allN_spec bindsL j hj)
  unfold ChainRecord.strongArrs
  rw [getElem!_pos _ j (by simp [strong_len]; omega)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [← h, List.getD_eq_getElem _ _ (by rw [strong_len]; omega)]

theorem bindsJL : Binds 3080 12 J1L.S 4 3 J1L.BP j1Chain.strongArrs j1Chain.baseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [ChainRecord.strongArrs, strong_len],
    strong_eqL, rfl, fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseL t ht)⟩

theorem chainCK : ChainCK 3080 12 J1L.S J1L.SI J1L.LR J1L.TR J1L.TRI 4 2 3 J1L.BP j1Chain.strongArrs
    j1Chain.baseArr derivs :=
  ⟨bindsJL, J1L.head, J1L.hl, card_le⟩

theorem elems_of_blocks {f : Nat → Bool} {c nb : Nat} (hc : c ≤ nb * 64)
    (h : ∀ s < nb, allBlk (s * 64) f 64 = true) : ∀ k < c, f k = true := by
  intro k hk
  have hs : k / 64 < nb := by omega
  have := allBlk_spec (h (k / 64) hs) (k % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (k / 64 * 64) (k % 64) = k := by
    change k / 64 * 64 + k % 64 = k
    omega
  rwa [e] at this

theorem tables_eq : j1Tables = levTables 3080 j1Chain.strongArrs j1Chain.baseArr 3 := by
  unfold j1Tables j1Levels levTables
  rw [chain_eq]

theorem orderTables_eq (m : Nat) :
    j1OrderTables m = filterProducts 3080 (ordTest 3080 m)
      (levTables 3080 j1Chain.strongArrs j1Chain.baseArr 3) (idT 3080) [] := by
  rw [j1OrderTables, tables_eq]

theorem lA_eq : j1A1List = j1Chain.generators.getD 0 [] := by rw [j1A1List, chain_eq]

theorem lB_eq : j1A2List = j1Chain.generators.getD 1 [] := by rw [j1A2List, chain_eq]

end CertificateChecks.KernelSporSch.J1

end
