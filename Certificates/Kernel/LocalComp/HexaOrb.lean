module

public import Certificates.Kernel.LocalComp.HexaEnum
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaOrbTests
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaTests

public section

namespace CertificateChecks.KernelLC.HexaOrb

open CFSG.KC.BfsPin CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HeSylow CertificateChecks.KernelLC

@[expose] noncomputable def conjK (m t : Nat) : Nat :=
  pcomp 64 7 (mask 7) m (pcomp 64 7 (mask 7) t (pinvS 64 7 (mask 7) m))

@[expose] noncomputable def PT0 : Nat := packA 7 hexaT0.toList

theorem kBindT : (Nat.beq hexaTGens.toArray.size HexaT.ng &&
    allN HexaT.ng fun k => bindArrK hexaTGens.toArray[k]! 64 7 (HexaT.G k)) = true := by quickRfl

theorem kBindM : (Nat.beq hexaMGens.toArray.size HexaM.ng &&
    allN HexaM.ng fun k => bindArrK hexaMGens.toArray[k]! 64 7 (HexaM.G k)) = true := by quickRfl

theorem kBindR : (Nat.beq hexaR0Gens.toArray.size HexaR.ng &&
    allN HexaR.ng fun k => bindArrK hexaR0Gens.toArray[k]! 64 7 (HexaR.G k)) = true := by quickRfl

theorem kT0 : (bindArrK hexaT0 64 7 PT0 && canonK 64 7 (mask 7) (64 * 7) PT0 &&
    canonK 64 7 (mask 7) (64 * 7) (pidn 64 7) && idK 64 7 (mask 7)) = true := by quickRfl

theorem kPerm : (allN HexaM.N fun j =>
    permOK 64 7 (mask 7) (64 * 7) (HexaM.T j) (pinvS 64 7 (mask 7) (HexaM.T j)) &&
      canonK 64 7 (mask 7) (64 * 7) (pinvS 64 7 (mask 7) (HexaM.T j))) = true := by quickRfl

theorem kOrb : ((List.range HexaT.N).all fun i => Nat.beq (HexaT.T i) (pidn 64 7) ||
    (decide (hexaOrbW[i]! < HexaM.N) &&
      (Nat.beq (conjK (HexaM.T hexaOrbW[i]!) (HexaT.T i)) PT0 ||
        (List.range HexaR.N).any fun r =>
          Nat.beq (conjK (HexaM.T hexaOrbW[i]!) (HexaT.T i)) (HexaR.T r)))) = true := by
  quickRfl

theorem eltsT : eltsN 64 hexaTGens = (List.range HexaT.N).map fun i => unpack 64 7 (HexaT.T i) := by
  obtain ⟨hs, hg⟩ := binds_of_check kBindT
  unfold eltsN certN
  rw [enumBfs_pts hs hg HexaT.ok (by decide)]
  exact pts_toList fun i => unpack 64 7 (HexaT.T i)

theorem eltsM : eltsN 64 hexaMGens = (List.range HexaM.N).map fun i => unpack 64 7 (HexaM.T i) := by
  obtain ⟨hs, hg⟩ := binds_of_check kBindM
  unfold eltsN certN
  rw [enumBfs_pts hs hg HexaM.ok (by decide)]
  exact pts_toList fun i => unpack 64 7 (HexaM.T i)

theorem eltsR : eltsN 64 hexaR0Gens = (List.range HexaR.N).map fun i => unpack 64 7 (HexaR.T i) := by
  obtain ⟨hs, hg⟩ := binds_of_check kBindR
  unfold eltsN certN
  rw [enumBfs_pts hs hg HexaR.ok (by decide)]
  exact pts_toList fun i => unpack 64 7 (HexaR.T i)

theorem hexaOrbCheck_eq : hexaOrbCheck = true := by
  have hT := bfsK_canon HexaT.ok
  have hM := bfsK_canon HexaM.ok
  have hR := bfsK_canon HexaR.ok
  have k0 := kT0
  simp only [Bool.and_eq_true] at k0
  obtain ⟨⟨⟨b0, c0⟩, cid⟩, hid⟩ := k0
  have e0 : hexaT0 = unpack 64 7 PT0 := unpack_eq_of_bindArrK b0
  have eid : idA 64 = unpack 64 7 (pidn 64 7) := (idK_sound hid).symm
  have hRl : ∀ q ∈ (List.range HexaR.N).map HexaR.T, canonK 64 7 (mask 7) (64 * 7) q = true := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
    exact hR r (List.mem_range.1 hr)
  unfold hexaOrbCheck
  simp only [eltsT, eltsM, eltsR, List.length_map, List.length_range]
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have kO := List.all_eq_true.1 kOrb i hi
  rw [getElem!_map_range _ hi', eid, eqA_unpack (hT i hi') cid]
  cases hd : decide (hexaOrbW[i]! < HexaM.N)
  · simp only [hd, Bool.false_and, Bool.or_false] at kO ⊢
    exact kO
  · have hj := of_decide_eq_true hd
    have kp := allN_spec kPerm _ hj
    rw [Bool.and_eq_true] at kp
    have hc : canonK 64 7 (mask 7) (64 * 7) (conjK (HexaM.T hexaOrbW[i]!) (HexaT.T i)) = true :=
      canonK_pcomp (hM _ hj) (canonK_pcomp (hT i hi') kp.2)
    rw [getElem!_map_range _ hj, conjA, invCand_unpack kp.1, compA_unpack (hT i hi') kp.2,
      compA_unpack (hM _ hj) (canonK_pcomp (hT i hi') kp.2), e0]
    change (Nat.beq _ _ || (true && (eqA 64 (unpack 64 7 (conjK _ _)) (unpack 64 7 PT0) ||
      inLN 64 (List.map (fun r => unpack 64 7 (HexaR.T r)) (List.range HexaR.N))
        (unpack 64 7 (conjK _ _))))) = true
    have eR : List.map (fun r => unpack 64 7 (HexaR.T r)) (List.range HexaR.N) =
        ((List.range HexaR.N).map HexaR.T).map (unpack 64 7) := by
      rw [List.map_map]
      rfl
    rw [eqA_unpack hc c0, inLN, eR, any_eqA_unpack hc hRl, List.any_map]
    simp only [hd, Bool.true_and] at kO
    exact kO

end CertificateChecks.KernelLC.HexaOrb

end
