module

public import Certificates.Kernel.LocalQT.Base.C4061H
public import Certificates.Kernel.LocalQT.Base.C4061N
public import Certificates.Kernel.LocalQT.Base.C4061M
public import Certificates.Kernel.LocalQT.Base.C4061Z
public import Certificates.Kernel.LocalQT.Base.C4061P
public import Certificates.Kernel.LocalQT.Base.C4076B
public import Certificates.Kernel.LocalQT.Base.C4143
public import CFSG.Certificates.Kernel.LocalQTX1RSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4061

open CFSG.KC.LQT.XR CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Ru.Native (ruData)

theorem foldl_slpStepA_size (ext : List (Nat × Nat)) (acc : Array (Array Nat)) :
    (ext.foldl slpStepA acc).size = acc.size + ext.length := by
  induction ext generalizing acc with
  | nil => rfl
  | cons p ext ih =>
    rw [List.foldl_cons, ih]
    simp [slpStepA]
    omega

theorem foldl_slpStepA_get (ext : List (Nat × Nat)) (acc : Array (Array Nat)) (i : Nat)
    (hi : i < acc.size) : (ext.foldl slpStepA acc)[i]! = acc[i]! := by
  induction ext generalizing acc with
  | nil => rfl
  | cons p ext ih =>
    rw [List.foldl_cons, ih _ (by simp [slpStepA]; omega)]
    have h2 : i < (acc.push (compArr acc[p.1]! acc[p.2]!)).size := by simp; omega
    simp only [slpStepA]
    rw [getElem!_pos (acc.push (compArr acc[p.1]! acc[p.2]!)) i h2, getElem!_pos acc i hi,
      Array.getElem_push_lt hi]

theorem slpTabsA_append_get (ta tb : Array Nat) (prog ext : List (Nat × Nat)) (i : Nat)
    (hi : i < prog.length + 2) :
    (slpTabsA ta tb (prog ++ ext))[i]! = (slpTabsA ta tb prog)[i]! := by
  unfold slpTabsA
  rw [List.foldl_append, foldl_slpStepA_get]
  rw [foldl_slpStepA_size]
  simp
  omega

theorem ta'_eq : ruTa' = C4143.ta.toArray := C4143.ta_eq

theorem tb'_eq : ruTb' = C4143.tb.toArray := C4143.tb_eq

theorem nt2_get (i : Nat) (hi : i < ruProg.length + 2) : ruNT2[i]! = ruSLP[i]! :=
  slpTabsA_append_get ruTa ruTb ruProg ruExt i hi

theorem qp_lt : ∀ p ∈ ruQp, p.1 < ruProg.length + 2 ∧ p.2 < ruProg.length + 2 := by
  intro p hp
  simp only [ruQp, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h <;> subst h <;> decide

theorem gens_eq : ruGens2 = ruQp.map fun p => ruSLP[p.1]! :=
  List.map_congr_left fun p hp => nt2_get p.1 (qp_lt p hp).1

theorem gensI_eq : ruGensI2 = ruQp.map fun p => ruSLP[p.2]! :=
  List.map_congr_left fun p hp => nt2_get p.2 (qp_lt p hp).2

theorem enum_eq : ruEnum2 = ruEnum := by
  unfold ruEnum2 ruEnum
  rw [gens_eq, gensI_eq]
  rfl

theorem valid : slpValidAux P2 2 = true := by quickRfl

theorem wvalid : slpValidAux WP 2 = true := by quickRfl

theorem cert : (slpValidAux ruProg2 2 = true)
    ∧ (slpValidAux ruWprog 2 = true)
    ∧ (qpOK ruData.n ruNT2 ruQp)
    ∧ (BaseEnumOK ruData.n ruB' ruGens2 ruGensI2 ruEnum2.1 ruEnum2.2.1
          ruEnum2.2.2)
    ∧ (ruEnum2.1.size = 2 ^ 14)
    ∧ (ruGn < ruNT2.size ∧ ruGin < ruNT2.size ∧ ruHn < ruNT2.size ∧
          ruHin < ruNT2.size ∧ ruAn < ruWNT.size ∧ ruBn < ruWNT.size)
    ∧ (nodesLt ruNT2.size ruNodes1 = true ∧ nodesLt ruNT2.size ruNodes2 = true ∧
          nodesLt ruNT2.size ruNodes3 = true)
    ∧ (zClaimOK ruB'.length ruGens2 ruP ruEnum2.1 [Array.range ruData.n] ruL1 = true)
    ∧ (zClaimOK ruB'.length ruGens2 ruP ruEnum2.1 ruL1 ruL2 = true)
    ∧ (zClaimOK ruB'.length ruGens2 ruP ruEnum2.1 ruL2 ruL3 = true)
    ∧ (invPairOK (Array.range ruData.n) ruNT2[ruGn]! ruNT2[ruGin]! = true)
    ∧ (invPairOK (Array.range ruData.n) ruNT2[ruHn]! ruNT2[ruHin]! = true)
    ∧ (normOK ruL1 ruNT2[ruGn]! ruNT2[ruGin]! = true)
    ∧ (normOK ruL3 ruNT2[ruHn]! ruNT2[ruHin]! = true)
    ∧ (notNormOK ruL3 ruNT2[ruGn]! ruNT2[ruGin]! = true)
    ∧ (notNormOK ruL1 ruNT2[ruHn]! ruNT2[ruHin]! = true)
    ∧ (ruWNT[ruAn]! = ruTa')
    ∧ (ruWNT[ruBn]! = ruTb') := by
  have hA := x1RA_sound (hw := by norm_num) (h := ha) (hn2 := N.all) (hn3 := M.all)
  have hZ := zcl_sound (hw := by norm_num) (h := C4143.hd) (hnd := C4143.N.all)
    (hs := C4143.S.all) (hb := C4076.B.all) (hcov := by norm_num) (h2 := s2) (hn2 := N.all)
    (hz := zh) (hzs := Z.all)
  rw [← ta'_eq, ← tb'_eq] at hA hZ
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hA
  obtain ⟨z1, z2, z3⟩ := hZ
  have hb := C4143.cert
  unfold BaseCertS BaseCert at hb
  obtain ⟨-, -, -, -, -, -, -, -, -, henum, hsize, -⟩ := hb
  rw [List.map_map, List.map_map] at henum
  unfold ruP
  rw [enum_eq, gens_eq, gensI_eq]
  unfold ruL1 ruL2 ruL3 ruWNT ruNT2
  rw [prog2_eq, wprog_eq]
  exact ⟨valid, wvalid, a1, henum, hsize, a2, a3, z1, z2, z3, a4, a5, a6, a7, a8, a9, a10, a11⟩

end CFSG.KD.LQT.C4061

end
