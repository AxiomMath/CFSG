module

public import Certificates.Kernel.SporSch.Tits.Help
public import Certificates.Kernel.SporSch.Tits.GenSurv
public import Certificates.Kernel.SporSch.Tits.GenAll5
public import CFSG.Certificates.Kernel.SporSch.TitsEnum5Sound
public import Certificates.Kernel.Sporadic.Tits.LocS
public import Certificates.Kernel.Sporadic.Tits.LocH
public import Certificates.Kernel.Sporadic.Tits.LocN
public import Certificates.Kernel.Sporadic.Tits.LocJ
public import Certificates.Kernel.Sporadic.Tits.LocK
meta import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Std.Tactic.BVDecide.Normalize.Bool

public section

set_option maxRecDepth 400000

#kst_surv CertificateChecks.KernelSporSch.TitsCHJ 11 CFSG.Sporadic.Schreier.Tits.titsHLevels
  CFSG.Sporadic.Schreier.Tits.titsCHJ
#kst_surv CertificateChecks.KernelSporSch.TitsCNK 11 CFSG.Sporadic.Schreier.Tits.titsNLevels
  CFSG.Sporadic.Schreier.Tits.titsCNK

namespace CertificateChecks.KernelSporSch.TitsCentral

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp

theorem canS : allN 9 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (TitsS.S j)) = true := by
  quickRfl
theorem canH : allN 9 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (TitsH.S j)) = true := by
  quickRfl
theorem canJ : allN 9 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (TitsJ.S j)) = true := by
  quickRfl
theorem canK : allN 7 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (TitsK.S j)) = true := by
  quickRfl
theorem canId : canonK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) = true := by quickRfl
theorem idOK : idK 1755 11 (mask 11) = true := by quickRfl

theorem id_eq : idA 1755 = unpack 1755 11 (pidn 1755 11) := (idK_sound idOK).symm

theorem commAll_eq {gens : Array (Array Nat)} {G : Nat → Nat} {k x : Nat} (hs : gens.size = k)
    (hg : ∀ i < k, gens[i]! = unpack 1755 11 (G i)) (hc : ∀ i < k, C (G i)) (hx : C x) :
    commutesAll 1755 (unpack 1755 11 x) gens = TitsHelp.commK G k x := by
  unfold commutesAll TitsHelp.commK
  rw [hs]
  exact allLt_eq_allN fun i hi => by rw [hg i hi, eq22_sound hx (hc i hi)]

theorem commAll5_eq {gens : Array (Array Nat)} {G : Nat → Nat} {k t0 t1 t2 t3 t4 : Nat}
    (hs : gens.size = k) (hg : ∀ i < k, gens[i]! = unpack 1755 11 (G i)) (hc : ∀ i < k, C (G i))
    (h0 : C t0) (h1 : C t1) (h2 : C t2) (h3 : C t3) (h4 : C t4) :
    commutesAll 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) gens =
      commAllPts 1755 11 (mask 11) G k t0 t1 t2 t3 t4 := by
  unfold commutesAll commAllPts
  rw [hs]
  exact allLt_eq_allN fun i hi => by rw [hg i hi, commPts_sound h0 h1 h2 h3 h4 (hc i hi)]

theorem comm_eq {A : Array (Array Nat)} {PS : Nat → Nat} {kS nb BP k x : Nat} {base : Array Nat}
    (hb : Binds 1755 11 PS kS nb BP A base) (hk : k ≤ kS)
    (hc : allN kS (fun j => canonK 1755 11 (mask 11) (1755 * 11) (PS j)) = true) (hx : C x) :
    commutesAll 1755 (unpack 1755 11 x) (A.extract 0 k) = commK PS k x := by
  have hs : A.size = kS := hb.2.2.2.1
  refine commAll_eq (ext_size (by omega)) (fun i hi => ?_) (fun i hi => allN_spec hc i (by omega)) hx
  rw [ext_get (by omega) hi]
  exact hb.2.2.2.2.1 i (by omega)

theorem comm5_eq {A : Array (Array Nat)} {PS : Nat → Nat} {kS nb BP k t0 t1 t2 t3 t4 : Nat}
    {base : Array Nat} (hb : Binds 1755 11 PS kS nb BP A base) (hk : k ≤ kS)
    (hc : allN kS (fun j => canonK 1755 11 (mask 11) (1755 * 11) (PS j)) = true)
    (h0 : C t0) (h1 : C t1) (h2 : C t2) (h3 : C t3) (h4 : C t4) :
    commutesAll 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) (A.extract 0 k) =
      commAllPts 1755 11 (mask 11) PS k t0 t1 t2 t3 t4 := by
  have hs : A.size = kS := hb.2.2.2.1
  refine commAll5_eq (ext_size (by omega)) (fun i hi => ?_) (fun i hi => allN_spec hc i (by omega))
    h0 h1 h2 h3 h4
  rw [ext_get (by omega) hi]
  exact hb.2.2.2.2.1 i (by omega)

@[expose] noncomputable def PS (t0 t1 t2 t3 t4 : Nat) : Bool :=
  bIf(commAllPts 1755 11 (mask 11) TitsS.S 3 t0 t1 t2 t3 t4,
    bIf(eqPts 1755 11 (mask 11) (pidn 1755 11) t0 t1 t2 t3 t4, true,
      eqPts 1755 11 (mask 11) TitsZ t0 t1 t2 t3 t4), true)

@[expose] noncomputable def QS : Nat → Nat → Nat → Nat → Nat → Nat → Bool := fun _ => PS

#kst_all5 CertificateChecks.KernelSporSch.TitsSE 1755 11 8 2 TitsS.LR TitsS.TR QS

theorem centerS : all5 1755 titsSLevels (fun a => !(commutesAll 1755 a (titsSArrs.extract 0 3)) ||
    eqA 1755 a (idA 1755) || eqA 1755 a titsZArr) = true := by
  refine all5K_sound bindsS permS TitsS.hl (fun t0 t1 t2 t3 t4 c0 c1 c2 c3 c4 _ h => ?_) TitsSE.all
  rw [comm5_eq bindsS (by norm_num) canS c0 c1 c2 c3 c4, id_eq, z_eq,
    ← eqPts_sound c0 c1 c2 c3 c4 canId, ← eqPts_sound c0 c1 c2 c3 c4 canonZ]
  cases hc : commAllPts 1755 11 (mask 11) TitsS.S 3 t0 t1 t2 t3 t4
  · rfl
  · rw [hc] at h
    cases h1 : eqPts 1755 11 (mask 11) (pidn 1755 11) t0 t1 t2 t3 t4
    · rw [h1] at h
      simp [h]
    · simp

@[expose] noncomputable def QH : Nat → Nat → Nat → Nat → Nat → Nat → Bool :=
  survQ (commAllPts 1755 11 (mask 11) TitsJ.S 4) TitsCHJ.M

#kst_all5 CertificateChecks.KernelSporSch.TitsHE 1755 11 10 8 TitsH.LR TitsH.TR QH

theorem mH : Nat.beq (maskOf TitsCHJ.C) TitsCHJ.M = true := by quickRfl
theorem aH : ascK (tot5 TitsH.LR) TitsCHJ.C 0 = true := by quickRfl
theorem zH : zipK (fun c l => Nat.beq (prodCode 1755 11 (mask 11) (1755 * 11) TitsH.LR TitsH.TR c) l)
    TitsCHJ.C TitsCHJ.L = true := by quickRfl

theorem chj_eq : titsCHJ = TitsCHJ.L.map (unpack 1755 11) :=
  surv5K_sound bindsH permH TitsH.hl (fun _ _ _ _ _ c0 c1 c2 c3 c4 =>
    (comm5_eq bindsJ (by norm_num) canJ c0 c1 c2 c3 c4).symm)
    mH aH zH TitsHE.all

@[expose] noncomputable def QN : Nat → Nat → Nat → Nat → Nat → Nat → Bool :=
  survQ (commAllPts 1755 11 (mask 11) TitsK.S 2) TitsCNK.M

#kst_all5 CertificateChecks.KernelSporSch.TitsNE 1755 11 24 2 TitsN.LR TitsN.TR QN

theorem mN : Nat.beq (maskOf TitsCNK.C) TitsCNK.M = true := by quickRfl
theorem aN : ascK (tot5 TitsN.LR) TitsCNK.C 0 = true := by quickRfl
theorem zN : zipK (fun c l => Nat.beq (prodCode 1755 11 (mask 11) (1755 * 11) TitsN.LR TitsN.TR c) l)
    TitsCNK.C TitsCNK.L = true := by quickRfl

theorem cnk_eq : titsCNK = TitsCNK.L.map (unpack 1755 11) :=
  surv5K_sound bindsN permN TitsN.hl (fun _ _ _ _ _ c0 c1 c2 c3 c4 =>
    (comm5_eq bindsK (by norm_num) canK c0 c1 c2 c3 c4).symm)
    mN aN zN TitsNE.all

@[expose] noncomputable def okHJ (c : Nat) : Bool :=
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) c,
  bAnd(permOK 1755 11 (mask 11) (1755 * 11) c (pinvS 1755 11 (mask 11) c),
  bAnd(commK TitsJ.S 4 c,
  bAnd(siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsH.LR TitsH.TRI TitsH.BP 5 0 c,
    siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsJ.LR TitsJ.TRI TitsJ.BP 4 0 c))))

@[expose] noncomputable def okNK (c : Nat) : Bool :=
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) c,
  bAnd(permOK 1755 11 (mask 11) (1755 * 11) c (pinvS 1755 11 (mask 11) c),
  bAnd(commK TitsK.S 2 c,
  bAnd(siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0 c,
    siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK.LR TitsK.TRI TitsK.BP 5 0 c))))

theorem kHJ : allL okHJ TitsCHJ.L = true := by quickRfl
theorem kNK : allL okNK TitsCNK.L = true := by quickRfl
theorem pHJ : pairNe TitsCHJ.L = true := by quickRfl
theorem pNK : pairNe TitsCNK.L = true := by quickRfl

theorem okHJ_spec {c : Nat} (hc : c ∈ TitsCHJ.L) :
    (isInvA 1755 (unpack 1755 11 c) (invCand 1755 (unpack 1755 11 c)) &&
      commutesAll 1755 (unpack 1755 11 c) (titsJArrs.extract 0 4) &&
      siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0 (unpack 1755 11 c) &&
      siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 (unpack 1755 11 c)) = true := by
  have h := allL_spec kHJ c hc
  unfold okHJ at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
  have s1 : siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0 (unpack 1755 11 c) = true :=
    siftK_soundR bindsH permH TitsH.hl rfl (hi_of h1) (range_of_canonK h1) h4
  have s2 : siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 (unpack 1755 11 c) = true :=
    siftK_soundR bindsJ permJ TitsJ.hl rfl (hi_of h1) (range_of_canonK h1) h5
  rw [isInv_of h2, comm_eq bindsJ (by norm_num) canJ h1, h3, s1, s2]
  rfl

theorem okNK_spec {c : Nat} (hc : c ∈ TitsCNK.L) :
    (isInvA 1755 (unpack 1755 11 c) (invCand 1755 (unpack 1755 11 c)) &&
      commutesAll 1755 (unpack 1755 11 c) (titsKArrs.extract 0 2) &&
      siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0 (unpack 1755 11 c) &&
      siftA 1755 titsKLevels (baseArr 1755 titsKBase) 0 (unpack 1755 11 c)) = true := by
  have h := allL_spec kNK c hc
  unfold okNK at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
  have s1 : siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0 (unpack 1755 11 c) = true :=
    siftK_soundR bindsN permN TitsN.hl rfl (hi_of h1) (range_of_canonK h1) h4
  have s2 : siftA 1755 titsKLevels (baseArr 1755 titsKBase) 0 (unpack 1755 11 c) = true :=
    siftK_soundR bindsK permK TitsK.hl rfl (hi_of h1) (range_of_canonK h1) h5
  rw [isInv_of h2, comm_eq bindsK (by norm_num) canK h1, h3, s1, s2]
  rfl

theorem canon_of_HJ {c : Nat} (hc : c ∈ TitsCHJ.L) : C c :=
  ((bAnd_iff _ _).1 (allL_spec kHJ c hc)).1

theorem canon_of_NK {c : Nat} (hc : c ∈ TitsCNK.L) : C c :=
  ((bAnd_iff _ _).1 (allL_spec kNK c hc)).1

theorem pair_of {L : List Nat} (hp : pairNe L = true) (hc : ∀ c ∈ L, C c) :
    (L.map (unpack 1755 11)).Pairwise (fun a b => eqA 1755 a b = false) := by
  rw [List.pairwise_map]
  exact (pairNe_spec hp).imp_of_mem fun ha hb h => by rw [eqA_unpack (hc _ ha) (hc _ hb)]; exact h

theorem zPerm : permOK 1755 11 (mask 11) (1755 * 11) TitsZ (pinvS 1755 11 (mask 11) TitsZ) = true := by
  quickRfl
theorem zS : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsS.LR TitsS.TRI TitsS.BP 5 0 TitsZ =
    true := by quickRfl
theorem zNe : neIdK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsZ = true := by quickRfl
theorem zSq : sqIdK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsZ = true := by quickRfl
theorem zCS : commK TitsS.S 3 TitsZ = true := by quickRfl
theorem zCH : commK TitsH.S 3 TitsZ = true := by quickRfl

theorem facts : titsSBase.length = 5 ∧ titsHBase.length = 5 ∧ titsNBase.length = 5 ∧
    all5 1755 titsSLevels (fun a => !(commutesAll 1755 a (titsSArrs.extract 0 3)) ||
      eqA 1755 a (idA 1755) || eqA 1755 a titsZArr) = true ∧
    all5 1755 titsHLevels (fun a => !(commutesAll 1755 a (titsJArrs.extract 0 4)) ||
      anyEq titsCHJ a) = true ∧
    all5 1755 titsNLevels (fun a => !(commutesAll 1755 a (titsKArrs.extract 0 2)) ||
      anyEq titsCNK a) = true ∧
    titsCHJ.length = 2 ∧ titsCNK.length = 4 ∧
    titsCHJ.all (fun c => isInvA 1755 c (invCand 1755 c) &&
      commutesAll 1755 c (titsJArrs.extract 0 4) &&
      siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0 c &&
      siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 c) = true ∧
    titsCNK.all (fun c => isInvA 1755 c (invCand 1755 c) &&
      commutesAll 1755 c (titsKArrs.extract 0 2) &&
      siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0 c &&
      siftA 1755 titsKLevels (baseArr 1755 titsKBase) 0 c) = true ∧
    titsCHJ.Pairwise (fun a b => eqA 1755 a b = false) ∧
    titsCNK.Pairwise (fun a b => eqA 1755 a b = false) ∧
    isInvA 1755 titsZArr (invCand 1755 titsZArr) = true ∧
    siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 titsZArr = true ∧
    eqA 1755 titsZArr (idA 1755) = false ∧
    eqA 1755 (compA 1755 titsZArr titsZArr) (idA 1755) = true ∧
    commutesAll 1755 titsZArr (titsSArrs.extract 0 3) = true ∧
    commutesAll 1755 titsZArr (titsHArrs.extract 0 3) = true := by
  refine ⟨by decide, by decide, by decide, centerS, all5_surv _ _, all5_surv _ _, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, siftK_soundR bindsS permS TitsS.hl z_eq (hi_of canonZ) (range_of_canonK canonZ) zS,
    ?_, ?_, ?_, ?_⟩
  · rw [chj_eq, List.length_map]
    rfl
  · rw [cnk_eq, List.length_map]
    rfl
  · rw [chj_eq, List.all_map, List.all_eq_true]
    exact fun c hc => okHJ_spec hc
  · rw [cnk_eq, List.all_map, List.all_eq_true]
    exact fun c hc => okNK_spec hc
  · rw [chj_eq]
    exact pair_of pHJ fun c hc => canon_of_HJ hc
  · rw [cnk_eq]
    exact pair_of pNK fun c hc => canon_of_NK hc
  · rw [z_eq]
    exact isInv_of zPerm
  · rw [z_eq]
    exact neIdK_sound zNe
  · rw [z_eq]
    exact sqIdK_sound zSq
  · rw [z_eq, comm_eq bindsS (by norm_num) canS canonZ]
    exact zCS
  · rw [z_eq, comm_eq bindsH (by norm_num) canH canonZ]
    exact zCH

end CertificateChecks.KernelSporSch.TitsCentral

end
