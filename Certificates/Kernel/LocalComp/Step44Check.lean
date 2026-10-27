module

public import Certificates.Kernel.LocalComp.Step44Enum
public import Certificates.Kernel.LocalComp.Step44EnumL
public import Certificates.Kernel.LocalComp.Step44EnumP
public import Certificates.Kernel.LocalComp.Step44EnumQ
public import Certificates.Kernel.LocalComp.HexaEnum
public import Certificates.Kernel.LocalComp.HeAutPin
public import Certificates.Kernel.LocalComp.HeSylowQECheck
public import CFSG.Certificates.Kernel.Step44KSound
public import CFSG.Certificates.Kernel.LocalCompUnpackList
public import CFSG.Certificates.Kernel.HeAutKSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.Step44Check

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.Step44K CFSG.KC.Enum CFSG.KS
open CFSG.KS.Prim CFSG.KS.Raw CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HeSylow CertificateChecks.KernelLC

@[expose] noncomputable def PV (i : Nat) : Nat := packA 7 (hexaV0.getD i #[]).toList

@[expose] noncomputable def Om : Nat := packA 7 hexaOmega.toList

@[expose] noncomputable def Mu : Nat := packA 7 hexaMu.toList

@[expose] noncomputable def MP (i : Nat) : Nat := hexaMuPi[i]!

@[expose] noncomputable def NFP : Nat := packA 2 hexaNF.toList

@[expose] noncomputable def gensP (n w g : Nat) (G : Nat → Nat) : Bool :=
  allN g fun k => permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k))

@[expose] noncomputable def bindL (gs : List (Array Nat)) (n w g : Nat) (G : Nat → Nat) : Bool :=
  Nat.beq gs.toArray.size g && allN g fun k =>
    Nat.beq gs.toArray[k]!.size n && bindListFromK gs.toArray[k]!.toList w (G k) 0

theorem bindA_eq {A : Array Nat} {n w P : Nat}
    (h : (Nat.beq A.size n && bindListFromK A.toList w P 0) = true) : A = unpack n w P := by
  rw [Bool.and_eq_true] at h
  have e := toArray_eq_of_bindListFromK h.2
  rw [Array.toArray_toList, Array.length_toList, Nat.eq_of_beq_eq_true h.1] at e
  exact e

theorem bindL_get {gs : List (Array Nat)} {n w g : Nat} {G : Nat → Nat}
    (h : bindL gs n w g G = true) :
    gs.toArray.size = g ∧ ∀ k < g, gs.toArray[k]! = unpack n w (G k) := by
  unfold bindL at h
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, fun k hk => bindA_eq (allN_spec h.2 k hk)⟩

theorem kV : (Nat.beq hexaV0.length 4 && allN 4 fun i => bindArrK hexaV0[i]! 64 7 (PV i) &&
    permOK 64 7 (mask 7) (64 * 7) (PV i) (pinvS 64 7 (mask 7) (PV i))) = true := by quickRfl

theorem kOmMu : (bindArrK hexaOmega 64 7 Om && bindArrK hexaMu 64 7 Mu &&
    permOK 64 7 (mask 7) (64 * 7) Om (pinvS 64 7 (mask 7) Om) &&
    permOK 64 7 (mask 7) (64 * 7) Mu (pinvS 64 7 (mask 7) Mu) && Nat.beq hexaMuPi.size 4) = true := by
  quickRfl

theorem kNF : (Nat.beq hexaNF.size 1024 && bindListFromK hexaNF.toList 2 NFP 0) = true := by quickRfl

theorem kBind64 : (bindL hexaMGens 64 7 HexaM.ng HexaM.G &&
    bindL (hexaV0 ++ [hexaOmega, hexaMu]) 64 7 S44K.ng S44K.G &&
    bindL [hexaOmega, hexaMu] 64 7 S44W.ng S44W.G && bindL hexaNormGens 64 7 S44H.ng S44H.G &&
    gensP 64 7 HexaM.ng HexaM.G && gensP 64 7 S44K.ng S44K.G && gensP 64 7 S44W.ng S44W.G &&
    gensP 64 7 S44H.ng S44H.G) = true := by quickRfl

theorem kBind256 : (bindL hexaNGens 256 9 S44N.ng S44N.G && bindL hexaNEGens 256 9 S44E.ng S44E.G &&
    bindL hexaPGens 256 9 S44P.ng S44P.G && bindL hexaPEGens 256 9 S44Q.ng S44Q.G &&
    gensP 256 9 S44N.ng S44N.G && gensP 256 9 S44E.ng S44E.G && gensP 256 9 S44P.ng S44P.G &&
    gensP 256 9 S44Q.ng S44Q.G) = true := by quickRfl

theorem kBindA : (bindL hexaAbImgs 32 6 S44Ab.ng S44Ab.G && bindL hexaAaImgs 16 5 S44Aa.ng S44Aa.G &&
    gensP 32 6 S44Ab.ng S44Ab.G && gensP 16 5 S44Aa.ng S44Aa.G) = true := by quickRfl

@[expose] noncomputable def lamG (g : Nat) (GP G : Nat → Nat) (ng : Nat) : Bool :=
  Nat.beq ng (8 + g) && (allN 8 fun k => Nat.beq (G k) (pmk 256 9 (starK PV (2 ^ k)))) &&
    (allN g fun k => Nat.beq (G (8 + k)) (GP k)) && gensP 256 9 (8 + g) G

theorem kLam : (lamG 0 S44P.G S44L.G S44L.ng && lamG 2 S44P.G S44LP.G S44LP.ng &&
    lamG 2 S44Q.G S44LQ.G S44LQ.ng && Nat.beq S44P.ng 2 && Nat.beq S44Q.ng 2) = true := by quickRfl

@[expose] noncomputable def pairG (m wa : Nat) (GB GA G : Nat → Nat) (ng : Nat) : Bool :=
  Nat.beq ng 10 && (allN 10 fun k => Nat.beq (G k) (pairK 256 m 9 wa (GB k) (GA k))) &&
    gensP (256 + m) 9 10 G

theorem kPair : (pairG 32 6 S44LP.G S44Ab.G S44PP.G S44PP.ng &&
    pairG 16 5 S44LQ.G S44Aa.G S44PQ.G S44PQ.ng) = true := by quickRfl

theorem kV0 : v0K PV Om Mu MP HexaM.N HexaM.T S44K.N S44K.T S44W.N S44W.T S44H.ng S44H.G = true := by
  quickRfl

theorem kTau : tauChk PV Om Mu MP NFP = true := by quickRfl

@[expose] noncomputable def aB (b : Nat) : Bool := autK PV Om Mu MP NFP S44N.N S44N.T (3 * b) 3

theorem a0 : aB 0 = true := by quickRfl

theorem a1 : aB 1 = true := by quickRfl

theorem a2 : aB 2 = true := by quickRfl

theorem a3 : aB 3 = true := by quickRfl

theorem a4 : aB 4 = true := by quickRfl

theorem a5 : aB 5 = true := by quickRfl

theorem a6 : aB 6 = true := by quickRfl

theorem a7 : aB 7 = true := by quickRfl

theorem a8 : aB 8 = true := by quickRfl

theorem a9 : aB 9 = true := by quickRfl

theorem a10 : aB 10 = true := by quickRfl

theorem a11 : aB 11 = true := by quickRfl

theorem a12 : aB 12 = true := by quickRfl

theorem a13 : aB 13 = true := by quickRfl

theorem a14 : aB 14 = true := by quickRfl

theorem a15 : aB 15 = true := by quickRfl

theorem kSm : smK PV S44N.ng S44N.G S44N.N S44N.T S44E.ng S44E.G S44E.N S44E.T S44P.ng S44P.G
    S44Q.ng S44Q.G HeAutY.ng HeAutY.G S44Ab.N S44Ab.T HeSylX.ng HeSylX.G S44Aa.N S44Aa.T = true := by
  quickRfl

theorem autK_add (lo a b : Nat) : autK PV Om Mu MP NFP S44N.N S44N.T lo (a + b) =
    (autK PV Om Mu MP NFP S44N.N S44N.T lo a && autK PV Om Mu MP NFP S44N.N S44N.T (lo + a) b) :=
  allR_add _ lo a b

theorem autK_join : ∀ m, (∀ b < m, aB b = true) → autK PV Om Mu MP NFP S44N.N S44N.T 0 (3 * m) = true
  | 0, _ => rfl
  | m + 1, h => by
    rw [Nat.mul_succ, autK_add, Nat.zero_add, autK_join m (fun b hb => h b (by omega)),
      Bool.true_and]
    exact h m (by omega)

theorem kAut : autK PV Om Mu MP NFP S44N.N S44N.T 0 48 = true :=
  autK_join 16 (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ
    (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ
    (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ
    (forall_lt_succ forall_lt_zero a0) a1) a2) a3) a4) a5) a6) a7) a8) a9) a10) a11) a12) a13)
    a14) a15)

theorem pinB {n w : Nat} {gs : List (Array Nat)} {g N : Nat} {G T E S : Nat → Nat}
    (hb : bindL gs n w g G = true) (hp : gensP n w g G = true) (hk : bfsK n w g G N T E S = true)
    (hf : N ≤ 4000) : Pin n w gs g G N T E S :=
  ⟨(bindL_get hb).1, (bindL_get hb).2, allN_spec hp, hk, hf⟩

theorem lamPin {g ng N : Nat} {GP G T E S : Nat → Nat} (h : lamG g GP G ng = true)
    (hk : bfsK 256 9 ng G N T E S = true) (hf : N ≤ 4000) : LamPin PV g GP G N T E S := by
  simp only [lamG, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have e := Nat.eq_of_beq_eq_true h1
  subst e
  exact ⟨fun k hk => Nat.eq_of_beq_eq_true (allN_spec h2 k hk),
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h3 k hk), allN_spec h4, hk, hf⟩

theorem pairPin {m wa ng N : Nat} {GB GA G T E S : Nat → Nat} (h : pairG m wa GB GA G ng = true)
    (hk : bfsK (256 + m) 9 ng G N T E S = true) (hf : N ≤ 4000) :
    PairPin m GB GA wa G N T E S := by
  simp only [pairG, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have e := Nat.eq_of_beq_eq_true h1
  subst e
  exact ⟨fun k hk => Nat.eq_of_beq_eq_true (allN_spec h2 k hk), allN_spec h3, hk, hf⟩

theorem step44Check_true : step44Check = true := by
  have kv := kV
  simp only [Bool.and_eq_true] at kv
  have ko := kOmMu
  simp only [Bool.and_eq_true] at ko
  obtain ⟨⟨⟨⟨bo, bm⟩, po⟩, pm⟩, hmp⟩ := ko
  have k64 := kBind64
  simp only [Bool.and_eq_true] at k64
  obtain ⟨⟨⟨⟨⟨⟨⟨bM, bK⟩, bW⟩, bH⟩, gM⟩, gK⟩, gW⟩, gH⟩ := k64
  have k256 := kBind256
  simp only [Bool.and_eq_true] at k256
  obtain ⟨⟨⟨⟨⟨⟨⟨bN, bE⟩, bP⟩, bQ⟩, gN⟩, gE⟩, gP⟩, gQ⟩ := k256
  have kA := kBindA
  simp only [Bool.and_eq_true] at kA
  obtain ⟨⟨⟨bAb, bAa⟩, gAb⟩, gAa⟩ := kA
  have kl := kLam
  simp only [Bool.and_eq_true] at kl
  obtain ⟨⟨⟨⟨lL, lLP⟩, lLQ⟩, -⟩, -⟩ := kl
  have kp := kPair
  simp only [Bool.and_eq_true] at kp
  have ky := HeAutCheck.kPermG
  simp only [Bool.and_eq_true] at ky
  have kx := HeSylowQECheck.kPerm16
  simp only [Bool.and_eq_true] at kx
  rw [step44Check_eq]
  exact step44K_sound
    ⟨Nat.eq_of_beq_eq_true kv.1, fun i hi => by
      have h := allN_spec kv.2 i hi
      simp only [Bool.and_eq_true] at h
      exact ⟨unpack_eq_of_bindArrK h.1, h.2⟩⟩
    (unpack_eq_of_bindArrK bo) (unpack_eq_of_bindArrK bm) po pm
    ⟨Nat.eq_of_beq_eq_true hmp, fun _ _ => rfl⟩ (bindA_eq kNF)
    (pinB bM gM HexaM.ok (by decide)) (pinB bK gK S44K.ok (by decide))
    (pinB bW gW S44W.ok (by decide)) (pinB bH gH S44H.ok (by decide))
    (pinB bN gN S44N.ok (by decide)) (pinB bE gE S44E.ok (by decide))
    (pinB bP gP S44P.ok (by decide)) (pinB bQ gQ S44Q.ok (by decide))
    (lamPin lL S44L.ok (by decide)) (lamPin lLP S44LP.ok (by decide))
    (lamPin lLQ S44LQ.ok (by decide))
    (pinB bAb gAb S44Ab.ok (by decide)) (HeAutCheck.pinY ky.1.1.1.1)
    (pinB bAa gAa S44Aa.ok (by decide))
    (HeSylowQECheck.pin16 HeSylowQECheck.kBindX16 kx.1.1.1.1 HeSylX.ok (by decide))
    (pairPin kp.1 S44PP.ok (by decide)) (pairPin kp.2 S44PQ.ok (by decide))
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl⟩
    kV0 kTau kAut kSm

end CertificateChecks.KernelLC.Step44Check

end
