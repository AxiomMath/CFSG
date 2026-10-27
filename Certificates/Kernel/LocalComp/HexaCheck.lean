module

public import Certificates.Kernel.LocalComp.HexaOrb
public import CFSG.Certificates.Kernel.HexaKSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HexaCheck

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.ComponentClassification.AS81.Hexa CertificateChecks.KernelLC
open CertificateChecks.KernelLC.HexaOrb
open CFSG.KLie.CT (andB orB notB)

theorem kBindC : (Nat.beq hexaCGens.toArray.size HexaC.ng &&
    allN HexaC.ng fun k => bindArrK hexaCGens.toArray[k]! 64 7 (HexaC.G k)) = true := by quickRfl

theorem kBindN : (Nat.beq hexaN0Gens.toArray.size HexaN.ng &&
    allN HexaN.ng fun k => bindArrK hexaN0Gens.toArray[k]! 64 7 (HexaN.G k)) = true := by quickRfl

@[expose] noncomputable def gensPerm (g : Nat) (G : Nat → Nat) : Bool :=
  allN g fun k => permOK 64 7 (mask 7) (64 * 7) (G k) (pinvS 64 7 (mask 7) (G k))

theorem kPermG : (gensPerm HexaT.ng HexaT.G && gensPerm HexaM.ng HexaM.G &&
    gensPerm HexaC.ng HexaC.G && gensPerm HexaN.ng HexaN.G && gensPerm HexaR.ng HexaR.G &&
    permOK 64 7 (mask 7) (64 * 7) PT0 (pinvS 64 7 (mask 7) PT0)) = true := by quickRfl

theorem pin {gs : List (Array Nat)} {g N : Nat} {G T E S : Nat → Nat}
    (hb : (Nat.beq gs.toArray.size g && allN g fun k => bindArrK gs.toArray[k]! 64 7 (G k)) = true)
    (hp : gensPerm g G = true) (hk : bfsK 64 7 g G N T E S = true) (hf : N ≤ 4000) :
    Pin 64 7 gs g G N T E S :=
  ⟨(binds_of_check hb).1, (binds_of_check hb).2, allN_spec hp, hk, hf⟩

theorem kGens : gensK 64 7 HexaT.ng HexaT.G HexaM.ng HexaM.G HexaC.ng HexaC.G HexaN.ng HexaN.G
    HexaR.ng HexaR.G HexaT.N HexaT.T HexaM.N HexaM.T HexaN.N HexaN.T PT0 = true := by quickRfl

theorem kCount : Nat.beq (countK 64 7 HexaM.N HexaM.T PT0) 48 = true := by quickRfl

theorem kMove : moveK 64 7 HexaM.N HexaM.T HexaC.ng HexaC.G HexaR.ng HexaR.G HexaR.N HexaR.T =
    true := by quickRfl

theorem kNormal : normalK 64 7 HexaT.N HexaT.T HexaC.N HexaC.T HexaN.N HexaN.T PT0 = true := by
  quickRfl

theorem kBlock : (blockK 64 7 4 HexaC.N HexaC.T hexaBlk4 hexaRep4 &&
    blockK 64 7 2 HexaC.N HexaC.T hexaBlk2 hexaRep2 &&
    faithfulK 64 7 HexaC.N HexaC.T hexaBlk4 hexaRep4 4 hexaBlk2 hexaRep2 2) = true := by quickRfl

theorem kFuse : fuseK 64 7 HexaT.N HexaT.T HexaM.N HexaM.T HexaN.N HexaN.T PT0
    hexaFuseW.1 hexaFuseW.2.1 hexaFuseW.2.2 = true := by quickRfl

@[expose] noncomputable def heavy (i : Nat) : Bool :=
  andB (Nat.beq (hexaOrbConj.getD i 0) 2160) (notB (Nat.beq i 0))

@[expose] noncomputable def oA (i : Nat) : Bool :=
  orbitAt 64 7 HexaT.T HexaM.N HexaM.T PT0 hexaOrbConj i

theorem oRest : (List.range 64).all (fun i => orB (heavy i) (oA i)) = true := by quickRfl

theorem heavyList : (List.range 64).all (fun i => notB (heavy i) ||
    [1, 2, 3, 4, 5, 6, 7, 16, 21, 27, 36, 44, 45, 49, 51, 52, 54, 63].contains i) = true := by
  quickRfl

theorem o1 : oA 1 = true := by quickRfl
theorem o2 : oA 2 = true := by quickRfl
theorem o3 : oA 3 = true := by quickRfl
theorem o4 : oA 4 = true := by quickRfl
theorem o5 : oA 5 = true := by quickRfl
theorem o6 : oA 6 = true := by quickRfl
theorem o7 : oA 7 = true := by quickRfl
theorem o16 : oA 16 = true := by quickRfl
theorem o21 : oA 21 = true := by quickRfl
theorem o27 : oA 27 = true := by quickRfl
theorem o36 : oA 36 = true := by quickRfl
theorem o44 : oA 44 = true := by quickRfl
theorem o45 : oA 45 = true := by quickRfl
theorem o49 : oA 49 = true := by quickRfl
theorem o51 : oA 51 = true := by quickRfl
theorem o52 : oA 52 = true := by quickRfl
theorem o54 : oA 54 = true := by quickRfl
theorem o63 : oA 63 = true := by quickRfl

theorem kOrbit : orbitK 64 7 HexaT.N HexaT.T HexaM.N HexaM.T PT0 hexaOrbConj = true := by
  have hN : HexaT.N = 64 := rfl
  unfold orbitK
  rw [hN, List.all_eq_true]
  intro i hi
  have hr := List.all_eq_true.1 oRest i hi
  have hl := List.all_eq_true.1 heavyList i hi
  change orB (heavy i) (oA i) = true at hr
  change oA i = true
  cases hh : heavy i
  · rw [hh] at hr
    exact hr
  · rw [hh] at hl
    have hl' : i ∈ [1, 2, 3, 4, 5, 6, 7, 16, 21, 27, 36, 44, 45, 49, 51, 52, 54, 63] := by
      simpa [notB] using hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
    rcases hl' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    exacts [o1, o2, o3, o4, o5, o6, o7, o16, o21, o27, o36, o44, o45, o49, o51, o52, o54, o63]

theorem hexaCheck_true : hexaCheck = true := by
  have kp := kPermG
  simp only [Bool.and_eq_true] at kp
  obtain ⟨⟨⟨⟨⟨pT, pM⟩, pC⟩, pN⟩, pR⟩, p0⟩ := kp
  have k0 := kT0
  simp only [Bool.and_eq_true] at k0
  have hb := kBlock
  simp only [Bool.and_eq_true] at hb
  rw [hexaCheck_eq]
  exact hexaK_sound (pin kBindT pT HexaT.ok (by decide)) (pin kBindM pM HexaM.ok (by decide))
    (pin kBindC pC HexaC.ok (by decide)) (pin kBindN pN HexaN.ok (by decide))
    (pin kBindR pR HexaR.ok (by decide)) (unpack_eq_of_bindArrK k0.1.1.1) p0
    ⟨rfl, rfl, rfl, rfl, rfl⟩ kGens kOrbit (Nat.eq_of_beq_eq_true kCount) kMove kNormal
    hb.1.1 hb.1.2 hb.2 kFuse

end CertificateChecks.KernelLC.HexaCheck

end
