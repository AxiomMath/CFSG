module

public import Certificates.Kernel.TcGen.McL
public import Certificates.Kernel.TcGen.Suz
public import Certificates.Kernel.TcGen.Fi22
public import Certificates.Kernel.TcGen.ON
public import CFSG.Certificates.Kernel.OpsLayMcertSound
public import Certificates.Data.CFSGNative.CTP.StrongP
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc

open CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.AGLEmbedding.R3 CFSG.Blueprint

theorem tc3_of {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {prog : List Op}
    {D : TSpec} (hw : D.wf = true) (h : seedsL c A B ⟨n, prog, D.facts⟩ D.rA D.rB = true) :
    tcCheck (ops3 d) sA sB n prog D = true := by
  obtain ⟨hm, hrA, hrB, h0, h1⟩ := seedsL_sound hc hp hd hA hB hsA hsB h
  dsimp only at hrA hrB h0 h1
  unfold tcCheck
  rw [hm, decide_eq_true hrA, decide_eq_true hrB, h0, h1, hw]
  rfl

theorem cp3_of {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {prog : List Op}
    {D : CpSpec} (hw : D.wf = true) (h : seedsL c A B ⟨n, prog, D.facts⟩ D.rA D.rB = true) :
    cpCheck (ops3 d) sA sB n prog D = true := by
  obtain ⟨hm, hrA, hrB, h0, h1⟩ := seedsL_sound hc hp hd hA hB hsA hsB h
  dsimp only at hrA hrB h0 h1
  unfold cpCheck
  rw [hm, decide_eq_true hrA, decide_eq_true hrB, h0, h1, hw]
  rfl

theorem cert9417 :
    (tcCheck (ops3 21) mclSylow5Data.seedA mclSylow5Data.seedB McLThree.tcNregs McLThree.tcProg
      McLThree.tcSpec = true) ∧
    (cpCheck (ops3 21) mclSylow5Data.seedA mclSylow5Data.seedB McLThree.cpNregs McLThree.cpProg
      McLThree.cpSpec = true) ∧ (McLThree.cpSpec.noFun = true) := by
  have hsA : mclSylow5Data.seedA = String.ofList McL.LA :=
    (rfl : mclSylow5Data.seedA = NativeSporadic.McLSeed1).trans McL.LA_eq
  have hsB : mclSylow5Data.seedB = String.ofList McL.LB :=
    (rfl : mclSylow5Data.seedB = NativeSporadic.McLSeed2).trans McL.LB_eq
  exact ⟨tc3_of McL.lay_ok rfl rfl McL.decA McL.decB hsA hsB (by decide +kernel) McL.tc_K,
    cp3_of McL.lay_ok rfl rfl McL.decA McL.decB hsA hsB (by decide +kernel) McL.cp_K,
    by decide +kernel⟩

theorem cert9500 :
    (tcCheck (ops3 64) NativeSporadic.SuzSeed1 NativeSporadic.SuzSeed2 SuzThree.tcNregs
      SuzThree.tcProg SuzThree.tcSpec = true) ∧
    (cpCheck (ops3 64) NativeSporadic.SuzSeed1 NativeSporadic.SuzSeed2 SuzThree.cpNregs
      SuzThree.cpProg SuzThree.cpSpec = true) ∧ (SuzThree.cpSpec.noFun = true) :=
  ⟨tc3_of Suz.lay_ok rfl rfl Suz.decA Suz.decB Suz.LA_eq Suz.LB_eq (by decide +kernel) Suz.tc_K,
    cp3_of Suz.lay_ok rfl rfl Suz.decA Suz.decB Suz.LA_eq Suz.LB_eq (by decide +kernel) Suz.cp_K,
    by decide +kernel⟩

theorem cert9501 :
    (tcCheck (ops3 77) NativeSporadic.Fi22Seed1 NativeSporadic.Fi22Seed2 Fi22Three.tcNregs
      Fi22Three.tcProg Fi22Three.tcSpec = true) ∧
    (cpCheck (ops3 77) NativeSporadic.Fi22Seed1 NativeSporadic.Fi22Seed2 Fi22Three.cpNregs
      Fi22Three.cpProg Fi22Three.cpSpec = true) ∧ (Fi22Three.cpSpec.noFun = true) :=
  ⟨tc3_of Fi22.lay_ok rfl rfl Fi22.decA Fi22.decB Fi22.LA_eq Fi22.LB_eq (by decide +kernel)
      Fi22.tc_K,
    cp3_of Fi22.lay_ok rfl rfl Fi22.decA Fi22.decB Fi22.LA_eq Fi22.LB_eq (by decide +kernel)
      Fi22.cp_K,
    by decide +kernel⟩

theorem cert9504 :
    (tcCheck (ops3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2 ONThree.tcNregs
      ONThree.tcProg ONThree.tcSpec = true) ∧
    (cpCheck (ops3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2 ONThree.cpNregs
      ONThree.cpProg ONThree.cpSpec = true) ∧ (ONThree.cpSpec.noFun = true) :=
  ⟨tc3_of ON.lay_ok rfl rfl ON.decA ON.decB ON.LA_eq ON.LB_eq (by decide +kernel) ON.tc_K,
    cp3_of ON.lay_ok rfl rfl ON.decA ON.decB ON.LA_eq ON.LB_eq (by decide +kernel) ON.cp_K,
    by decide +kernel⟩

end CertificateChecks.KernelTc

end
