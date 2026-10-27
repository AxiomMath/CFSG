module

public import Certificates.Kernel.LocalComp.HeModelCheckA
public import Certificates.Kernel.LocalComp.HeModelCheckU
public import Certificates.Kernel.LocalComp.HeModelCheckCA
public import Certificates.Kernel.LocalComp.HeModelCheckCN
public import Certificates.Kernel.LocalComp.HeModelCheckO

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeModelCheck

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.HeModelK CFSG.KC.Enum CFSG.KS
open CFSG.KS.Prim CFSG.KS.Raw CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HeTri CertificateChecks.KernelLC
open CertificateChecks.KernelLC.BindL CertificateChecks.KernelLC.HeModel
open CertificateChecks.KernelLC.HexaOrb (PT0)

theorem pinK {n w : Nat} {ps : List Nat} {gs : List (Array Nat)} {g N : Nat} {G T E S : Nat → Nat}
    {SK : List Nat} (hb : bindL gs n w g G = true) (hp : gensP n w g G = true)
    (hk : bfsK n w g G N T E S = true) (hK : keysSK n w ps N T SK = true) :
    PinB n w ps gs g G N T E S SK :=
  ⟨(bindL_get hb).1, (bindL_get hb).2, allN_spec hp, hk, hK⟩

theorem heModelCheck_true : heModelCheck = true := by
  have b64 := kBind64
  simp only [Bool.and_eq_true] at b64
  obtain ⟨⟨⟨⟨⟨⟨bT, bM⟩, bC⟩, bP⟩, bB⟩, bF⟩, bP23⟩ := b64
  have b32 := kBind32
  simp only [Bool.and_eq_true] at b32
  obtain ⟨⟨⟨⟨⟨bPC, bBC⟩, bP0⟩, bP1⟩, bU0⟩, bU1⟩ := b32
  have p64 := kPerm64
  simp only [Bool.and_eq_true] at p64
  obtain ⟨⟨⟨⟨⟨⟨pT, pM⟩, pC⟩, pP⟩, pB⟩, pF⟩, pP23⟩ := p64
  have p32 := kPerm32
  simp only [Bool.and_eq_true] at p32
  obtain ⟨⟨⟨⟨⟨pPC, pBC⟩, pP0⟩, pP1⟩, pU0⟩, pU1⟩ := p32
  have k64 := kKeys64
  simp only [Bool.and_eq_true] at k64
  obtain ⟨⟨⟨⟨kT, kM⟩, kP⟩, kB⟩, kF⟩ := k64
  have k32 := kKeys32
  simp only [Bool.and_eq_true] at k32
  obtain ⟨⟨⟨⟨kBC, kP0⟩, kP1⟩, kU0⟩, kU1⟩ := k32
  have zt := kZT
  simp only [Bool.and_eq_true] at zt
  obtain ⟨⟨⟨⟨⟨zB, zP⟩, tB⟩, tP⟩, cB⟩, cP⟩ := zt
  rw [heModelCheck_eq]
  exact heModelK_sound (h := heD) (k := hk)
    (pinK bT pT HexaT.ok kT) (pinK bM pM HexaM.ok kM) (pinK bP pP HeMP12.ok kP)
    (pinK bB pB HeMB0.ok kB) (pinK bF pF HeMF0.ok kF) (pinK bP23 pP23 HeMP23.ok kKeysP23)
    (pinK bPC pPC HeMC.ok kKeysC) (pinK bBC pBC HeMBC.ok kBC) (pinK bP0 pP0 HeMP0.ok kP0)
    (pinK bP1 pP1 HeMP1.ok kP1) (pinK bU0 pU0 HeMU0.ok kU0) (pinK bU1 pU1 HeMU1.ok kU1)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, (bindL_get bC).1, (bindL_get bC).2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (allN_spec pC)
    ⟨unpack_eq_of_bindArrK zB, zP⟩ ⟨unpack_eq_of_bindArrK tB, tP⟩ ⟨unpack_eq_of_bindArrK cB, cP⟩
    kZeta (fun i hi => allN_spec kOrb i hi) kB0 kFB ubAll kC caAll kFBC ucAll cnTotal kCount

end CertificateChecks.KernelLC.HeModelCheck

end
