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
import CFSG.Certificates.Kernel.SporSch.TitsCntBase
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

end CertificateChecks.KernelSporSch.TitsCentral

end

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsCentral

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp

theorem commBase_eq {A : Array (Array Nat)} {PS : Nat → Nat} {kS nb BP k x : Nat} {base : Array Nat}
    {f : Nat → Bool} (hb : Binds 1755 11 PS kS nb BP A base) (hk : k ≤ kS)
    (hf : ∀ j < k, f j = eqA 1755 (compA 1755 (unpack 1755 11 x) (unpack 1755 11 (PS j)))
      (compA 1755 (unpack 1755 11 (PS j)) (unpack 1755 11 x))) :
    commutesAll 1755 (unpack 1755 11 x) (A.extract 0 k) = allN k f := by
  have hs : A.size = kS := hb.2.2.2.1
  unfold commutesAll
  rw [ext_size (by omega)]
  refine allLt_eq_allN fun i hi => ?_
  rw [ext_get (by omega) hi, hb.2.2.2.2.1 i (by omega), hf i hi]

theorem canTr5 {kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) {t0 t1 t2 t3 t4 : Nat}
    (h : IsTr5 LR TR t0 t1 t2 t3 t4) : C t0 ∧ C t1 ∧ C t2 ∧ C t3 ∧ C t4 := by
  obtain ⟨⟨a0, h0, rfl⟩, ⟨a1, h1, rfl⟩, ⟨a2, h2, rfl⟩, ⟨a3, h3, rfl⟩, ⟨a4, h4, rfl⟩⟩ := h
  exact ⟨((lev_trAt hb hp hl (i := 0) (by omega)).2 a0 h0).1,
    ((lev_trAt hb hp hl (i := 1) (by omega)).2 a1 h1).1,
    ((lev_trAt hb hp hl (i := 2) (by omega)).2 a2 h2).1,
    ((lev_trAt hb hp hl (i := 3) (by omega)).2 a3 h3).1,
    ((lev_trAt hb hp hl (i := 4) (by omega)).2 a4 h4).1⟩

theorem bIf_or3 (a b c : Bool) : bIf(a, bIf(b, true, c), true) = (!a || b || c) := by
  cases a <;> cases b <;> rfl

theorem ndSc : (baseArr 1755 titsSBase).toList.Nodup := by decide
theorem ndHc : (baseArr 1755 titsHBase).toList.Nodup := by decide
theorem ndNc : (baseArr 1755 titsNBase).toList.Nodup := by decide

theorem siftSS : allN 3 (fun j => siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsS.LR
    TitsS.TRI TitsS.BP 5 0 (TitsS.S j)) = true := by quickRfl
theorem siftJH : allN 4 (fun j => siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsH.LR
    TitsH.TRI TitsH.BP 5 0 (TitsJ.S j)) = true := by quickRfl
theorem siftKN : allN 2 (fun j => siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR
    TitsN.TRI TitsN.BP 5 0 (TitsK.S j)) = true := by quickRfl

theorem memSS {j : Nat} (hj : j < 3) : siftA 1755 (rawLevels 1755 titsSArrs (baseArr 1755 titsSBase))
    (baseArr 1755 titsSBase) 0 (unpack 1755 11 (TitsS.S j)) = true :=
  siftK_soundR bindsS permS TitsS.hl rfl (hi_of (allN_spec canS j (by omega)))
    (range_of_canonK (allN_spec canS j (by omega))) (allN_spec siftSS j hj)
theorem memJH {j : Nat} (hj : j < 4) : siftA 1755 (rawLevels 1755 titsHArrs (baseArr 1755 titsHBase))
    (baseArr 1755 titsHBase) 0 (unpack 1755 11 (TitsJ.S j)) = true :=
  siftK_soundR bindsH permH TitsH.hl rfl (hi_of (allN_spec canJ j (by omega)))
    (range_of_canonK (allN_spec canJ j (by omega))) (allN_spec siftJH j hj)
theorem memKN {j : Nat} (hj : j < 2) : siftA 1755 (rawLevels 1755 titsNArrs (baseArr 1755 titsNBase))
    (baseArr 1755 titsNBase) 0 (unpack 1755 11 (TitsK.S j)) = true :=
  siftK_soundR bindsN permN TitsN.hl rfl (hi_of (allN_spec canK j (by omega)))
    (range_of_canonK (allN_spec canK j (by omega))) (allN_spec siftKN j hj)

noncomputable def PS (t0 t1 t2 t3 t4 : Nat) : Bool :=
  bIf(allN 3 (fun j => baseComm TitsS.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (TitsS.S j))),
    bIf(eqPts 1755 11 (mask 11) (pidn 1755 11) t0 t1 t2 t3 t4, true,
      eqPts 1755 11 (mask 11) TitsZ t0 t1 t2 t3 t4), true)

noncomputable def QS: Nat → Nat → Nat → Nat → Nat → Nat → Bool := fun _ => PS

#kst_all5 CertificateChecks.KernelSporSch.TitsSE 1755 11 8 2 TitsS.LR TitsS.TR QS

theorem agrCS : Agrees TitsS.LR TitsS.TR PS (fun a => !(commutesAll 1755 a (titsSArrs.extract 0 3)) ||
    eqA 1755 a (idA 1755) || eqA 1755 a titsZArr) := fun t0 t1 t2 t3 t4 h => by
  obtain ⟨c0, c1, c2, c3, c4⟩ := canTr5 bindsS permS TitsS.hl h
  dsimp only
  rw [commBase_eq bindsS (by norm_num) fun j hj => baseCommGE_eq bindsS TitsS.head TitsS.hl (NS := 220)
      (CH := 8) (by norm_num) TitsS.hs ndSc h (allN_spec canS j (by omega)) (memSS hj),
    id_eq, z_eq, ← eqPts_sound c0 c1 c2 c3 c4 canId, ← eqPts_sound c0 c1 c2 c3 c4 canonZ]
  exact bIf_or3 _ _ _

noncomputable def centPH (t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 4 (fun j => baseComm TitsH.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (TitsJ.S j)))

noncomputable def QH: Nat → Nat → Nat → Nat → Nat → Nat → Bool := survQ centPH TitsCHJ.M

#kst_all5 CertificateChecks.KernelSporSch.TitsHE 1755 11 10 8 TitsH.LR TitsH.TR QH

theorem mH : Nat.beq (maskOf TitsCHJ.C) TitsCHJ.M = true := by quickRfl
theorem aH : ascK (tot5 TitsH.LR) TitsCHJ.C 0 = true := by quickRfl
theorem zH : zipK (fun c l => Nat.beq (prodCode 1755 11 (mask 11) (1755 * 11) TitsH.LR TitsH.TR c) l)
    TitsCHJ.C TitsCHJ.L = true := by quickRfl

theorem agrCH : Agrees TitsH.LR TitsH.TR centPH (fun a => commutesAll 1755 a (titsJArrs.extract 0 4)) :=
  fun _ _ _ _ _ h => (commBase_eq bindsJ (by norm_num) fun j hj => baseCommGE_eq bindsH TitsH.head
    TitsH.hl (NS := 220) (CH := 8) (by norm_num) TitsH.hs ndHc h (allN_spec canJ j (by omega))
    (memJH hj)).symm

noncomputable def centPN (t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 2 (fun j => baseComm TitsN.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (TitsK.S j)))

noncomputable def QN: Nat → Nat → Nat → Nat → Nat → Nat → Bool := survQ centPN TitsCNK.M

#kst_all5 CertificateChecks.KernelSporSch.TitsNE 1755 11 24 2 TitsN.LR TitsN.TR QN

theorem mN : Nat.beq (maskOf TitsCNK.C) TitsCNK.M = true := by quickRfl
theorem aN : ascK (tot5 TitsN.LR) TitsCNK.C 0 = true := by quickRfl
theorem zN : zipK (fun c l => Nat.beq (prodCode 1755 11 (mask 11) (1755 * 11) TitsN.LR TitsN.TR c) l)
    TitsCNK.C TitsCNK.L = true := by quickRfl

theorem agrCN : Agrees TitsN.LR TitsN.TR centPN (fun a => commutesAll 1755 a (titsKArrs.extract 0 2)) :=
  fun _ _ _ _ _ h => (commBase_eq bindsK (by norm_num) fun j hj => baseCommGE_eq bindsN TitsN.head
    TitsN.hl (NS := 220) (CH := 8) (by norm_num) TitsN.hs ndNc h (allN_spec canK j (by omega))
    (memKN hj)).symm

end CertificateChecks.KernelSporSch.TitsCentral

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsCentral

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp

theorem centerS : all5 1755 titsSLevels (fun a => !(commutesAll 1755 a (titsSArrs.extract 0 3)) ||
    eqA 1755 a (idA 1755) || eqA 1755 a titsZArr) = true :=
  all5K_soundA bindsS permS TitsS.hl agrCS TitsSE.all

theorem chj_eq : titsCHJ = TitsCHJ.L.map (unpack 1755 11) := by
  refine (surv5K_soundCT bindsH permH TitsH.hl agrCH mH aH TitsHE.all).trans ?_
  rw [zipK_beq_map zH, List.map_map]
  rfl

theorem cnk_eq : titsCNK = TitsCNK.L.map (unpack 1755 11) := by
  refine (surv5K_soundCT bindsN permN TitsN.hl agrCN mN aN TitsNE.all).trans ?_
  rw [zipK_beq_map zN, List.map_map]
  rfl

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

theorem fBases : titsSBase.length = 5 ∧ titsHBase.length = 5 ∧ titsNBase.length = 5 :=
  ⟨by decide, by decide, by decide⟩

theorem fSurvH : all5 1755 titsHLevels (fun a => !(commutesAll 1755 a (titsJArrs.extract 0 4)) ||
    anyEq titsCHJ a) = true := all5_surv _ _

theorem fSurvN : all5 1755 titsNLevels (fun a => !(commutesAll 1755 a (titsKArrs.extract 0 2)) ||
    anyEq titsCNK a) = true := all5_surv _ _

theorem fLenHJ : titsCHJ.length = 2 := by
  rw [chj_eq, List.length_map]
  rfl

theorem fLenNK : titsCNK.length = 4 := by
  rw [cnk_eq, List.length_map]
  rfl

theorem fAllHJ : titsCHJ.all (fun c => isInvA 1755 c (invCand 1755 c) &&
      commutesAll 1755 c (titsJArrs.extract 0 4) &&
      siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0 c &&
      siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 c) = true := by
  rw [chj_eq, List.all_eq_true]
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  exact okHJ_spec hc'

theorem fAllNK : titsCNK.all (fun c => isInvA 1755 c (invCand 1755 c) &&
      commutesAll 1755 c (titsKArrs.extract 0 2) &&
      siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0 c &&
      siftA 1755 titsKLevels (baseArr 1755 titsKBase) 0 c) = true := by
  rw [cnk_eq, List.all_eq_true]
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  exact okNK_spec hc'

theorem fPairHJ : titsCHJ.Pairwise (fun a b => eqA 1755 a b = false) := by
  rw [chj_eq]
  exact pair_of pHJ fun c hc => canon_of_HJ hc

theorem fPairNK : titsCNK.Pairwise (fun a b => eqA 1755 a b = false) := by
  rw [cnk_eq]
  exact pair_of pNK fun c hc => canon_of_NK hc

theorem fZInv : isInvA 1755 titsZArr (invCand 1755 titsZArr) = true := by
  rw [z_eq]
  exact isInv_of zPerm

theorem fZSift : siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 titsZArr = true :=
  siftK_soundR bindsS permS TitsS.hl z_eq (hi_of canonZ) (range_of_canonK canonZ) zS

theorem fZNe : eqA 1755 titsZArr (idA 1755) = false := by
  rw [z_eq]
  exact neIdK_sound zNe

theorem fZSq : eqA 1755 (compA 1755 titsZArr titsZArr) (idA 1755) = true := by
  rw [z_eq]
  exact sqIdK_sound zSq

theorem fZCS : commutesAll 1755 titsZArr (titsSArrs.extract 0 3) = true := by
  rw [z_eq, comm_eq bindsS (by norm_num) canS canonZ]
  exact zCS

theorem fZCH : commutesAll 1755 titsZArr (titsHArrs.extract 0 3) = true := by
  rw [z_eq, comm_eq bindsH (by norm_num) canH canonZ]
  exact zCH

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
    commutesAll 1755 titsZArr (titsHArrs.extract 0 3) = true :=
  ⟨fBases.1, fBases.2.1, fBases.2.2, centerS, fSurvH, fSurvN, fLenHJ, fLenNK, fAllHJ, fAllNK,
    fPairHJ, fPairNK, fZInv, fZSift, fZNe, fZSq, fZCS, fZCH⟩

end CertificateChecks.KernelSporSch.TitsCentral

end
