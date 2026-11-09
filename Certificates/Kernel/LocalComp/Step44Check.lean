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
import CFSG.Certificates.Kernel.HexaStabKGlue

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

open CFSG.KLie.CT (sumN)

theorem strictN_eqV (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eqV (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def cjV0 (m v v' : Nat) : Bool :=
  allN 64 fun x => Nat.beq (pg 7 (mask 7) m (pg 7 (mask 7) v x)) (pg 7 (mask 7) v' (pg 7 (mask 7) m x))

@[expose] noncomputable def nvI (PV : Nat → Nat) (m : Nat) : Bool :=
  allN 4 fun i => CFSG.KLie.CT.anyN 4 fun j => cjV0 m (PV i) (PV j)

@[expose] noncomputable def sixI (PV : Nat → Nat) (m : Nat) : Bool :=
  CFSG.KLie.CT.andB
    (allN 3 fun u => Nat.beq (Nat.div (pg 7 (mask 7) m (Nat.mul 16 (Nat.succ u))) 16) (Nat.succ u))
    (allN 4 fun j => cjV0 m (PV j) (PV j))

theorem conj_cjV0 {m v v' : Nat} (hm : PP 64 7 m) (hv : PP 64 7 v) (hv' : PP 64 7 v') :
    Nat.beq (conj 64 7 m v) v' = cjV0 m v v' := by
  have hw : (64 : Nat) < 2 ^ 7 := by decide
  have h32 : (64 : Nat) < 2 ^ 32 := by decide
  have hc : conj 64 7 m v =
      pcomp 64 7 (mask 7) m (pcomp 64 7 (mask 7) v (pinvS 64 7 (mask 7) m)) := by
    simp only [conj, mul, inv, strictN_eqV]
  have hpc : PP 64 7 (conj 64 7 m v) := hc ▸ hm.mul (hv.mul hm.inv)
  have ev : ∀ x < 64, pg 7 (mask 7) (conj 64 7 m v) x =
      pg 7 (mask 7) m (pg 7 (mask 7) v (pg 7 (mask 7) (pinvS 64 7 (mask 7) m) x)) := by
    intro x hx
    rw [hc, CFSG.KS.PF.pg_pcomp h32 hx, CFSG.KS.PF.pg_pcomp h32 hx]
  have l1 : ∀ y < 64, pg 7 (mask 7) (pinvS 64 7 (mask 7) m) (pg 7 (mask 7) m y) = y :=
    fun y hy => CFSG.KS.PinvS.pg_pinvS hw hm.2 hy
  have lt := (CFSG.KS.PF.canon_facts hm.1).2.2.2
  unfold cjV0
  rw [allN_eq']
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true]
  constructor
  · intro h x hx
    have hx' := List.mem_range.1 hx
    rw [← Nat.eq_of_beq_eq_true h, ev _ (lt x hx'), l1 x hx']
    exact Nat.beq_refl _
  · intro h
    have e : conj 64 7 m v = v' :=
      CFSG.KS.PF.eq_of_fields (by decide : 0 < 7) (CFSG.KS.PF.canon_facts hpc.1).2.2.1
        (CFSG.KS.PF.canon_facts hv'.1).2.2.1 fun x hx => by
          obtain ⟨y, hy, rfl⟩ := CFSG.KS.PinvS.surj_of_injK hm.2 x hx
          rw [ev _ (lt y hy), l1 y hy]
          exact Nat.eq_of_beq_eq_true (h y (List.mem_range.2 hy))
    rw [e]
    exact Nat.beq_refl _

theorem allN_congrV {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    allN n f = allN n g := by
  rw [allN_eq', allN_eq']
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range]
  exact ⟨fun H i hi => by rw [← h i hi]; exact H i hi, fun H i hi => by rw [h i hi]; exact H i hi⟩

theorem anyN_congrV {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    CFSG.KLie.CT.anyN n f = CFSG.KLie.CT.anyN n g := by
  rw [anyN_eq, anyN_eq]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range]
  exact ⟨fun ⟨i, hi, e⟩ => ⟨i, hi, by rw [← h i hi]; exact e⟩,
    fun ⟨i, hi, e⟩ => ⟨i, hi, by rw [h i hi]; exact e⟩⟩

theorem normV0_eqI {PV : Nat → Nat} (hPV : ∀ i < 4, PP 64 7 (PV i)) {m : Nat} (hm : PP 64 7 m) :
    normV0 PV m = nvI PV m := by
  unfold normV0 nvI inV0
  exact allN_congrV fun i hi => by
    rw [strictB_eqV]
    exact anyN_congrV fun j hj => conj_cjV0 hm (hPV i hi) (hPV j hj)

theorem sixTriv_eqI {PV : Nat → Nat} (hPV : ∀ i < 4, PP 64 7 (PV i)) {m : Nat} (hm : PP 64 7 m) :
    sixTriv PV m = sixI PV m := by
  unfold sixTriv sixI
  congr 1
  exact allN_congrV fun j hj => conj_cjV0 hm (hPV j hj) (hPV j hj)

@[expose] noncomputable def mValI (PV : Nat → Nat) (NK : Nat) (TK : Nat → Nat) (m : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) 145 0
      (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (fix16 m)) (inV0 PV m)))
    (Bool.rec (motive := fun _ => Nat) 145 1
      (CFSG.KLie.CT.andB (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (fix16 m)) (inV0 PV m))
      (CFSG.KLie.CT.andB
        (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (inV0 PV (pw 64 7 m 9))) (inL NK TK m))
      (CFSG.KLie.CT.andB (allN 16 fun v => Nat.blt (pg 7 (mask 7) m v) 16)
        (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (sixI PV m)) (inV0 PV m))))))
    (nvI PV m)

@[expose] noncomputable def mVal (PV : Nat → Nat) (NK : Nat) (TK : Nat → Nat) (m : Nat) : Nat :=
  strictN m fun m => mValI PV NK TK m

theorem mVal_spec {PV : Nat → Nat} (hPV : ∀ i < 4, PP 64 7 (PV i)) (NK : Nat) (TK : Nat → Nat)
    {m : Nat} (hm : PP 64 7 m) (h : mVal PV NK TK m ≤ 144) :
    CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (fix16 m)) (inV0 PV m) = true ∧
    CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (CFSG.KLie.CT.andB (normV0 PV m) (inV0 PV (pw 64 7 m 9))))
      (inL NK TK m) = true ∧
    CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (normV0 PV m))
      (allN 16 fun v => Nat.blt (pg 7 (mask 7) m v) 16) = true ∧
    CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (CFSG.KLie.CT.andB (normV0 PV m) (sixTriv PV m)))
      (inV0 PV m) = true ∧
    mVal PV NK TK m = Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (normV0 PV m) := by
  unfold mVal at h ⊢
  rw [strictN_eqV] at h ⊢
  rw [normV0_eqI hPV hm, sixTriv_eqI hPV hm]
  unfold mValI at h ⊢
  generalize nvI PV m = a at h ⊢
  generalize fix16 m = b at h ⊢
  generalize inV0 PV m = c at h ⊢
  generalize inV0 PV (pw 64 7 m 9) = d at h ⊢
  generalize inL NK TK m = e at h ⊢
  generalize (allN 16 fun v => Nat.blt (pg 7 (mask 7) m v) 16) = f at h ⊢
  generalize sixI PV m = g at h ⊢
  revert h
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> decide

theorem sumN_le_of {n : Nat} {f : Nat → Nat} : ∀ k < n, f k ≤ sumN n f := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    change f k ≤ f n + sumN n f
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · exact Nat.le_add_left_of_le (ih k hk)
    · subst hk; omega

theorem sumN_congrV {n : Nat} {f g : Nat → Nat} (h : ∀ k < n, f k = g k) : sumN n f = sumN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f n + sumN n f = g n + sumN n g
    rw [h n (Nat.lt_succ_self n), ih fun k hk => h k (Nat.lt_succ_of_lt hk)]

theorem kMV0 : Nat.beq (sumN HexaM.N fun k => mVal PV S44K.N S44K.T (HexaM.T k)) 144 = true := by
  quickRfl

theorem hPVf : ∀ i < 4, PP 64 7 (PV i) := by
  have hsz : szOK 64 7 = true := by decide
  have kv := kV
  simp only [Bool.and_eq_true] at kv
  exact fun i hi => PP_of_permOK hsz (by
    have h := allN_spec kv.2 i hi
    simp only [Bool.and_eq_true] at h
    exact h.2)

theorem kV0 : v0K PV Om Mu MP HexaM.N HexaM.T S44K.N S44K.T S44W.N S44W.T S44H.ng S44H.G = true := by
  have hPV := hPVf
  have k64 := kBind64
  simp only [Bool.and_eq_true] at k64
  have hM := PP_pts HexaM.ok (allN_spec k64.1.1.1.2)
  have hs := Nat.eq_of_beq_eq_true kMV0
  have sp := fun k (hk : k < HexaM.N) =>
    mVal_spec hPV S44K.N S44K.T (hM k hk) (by
      have e := sumN_le_of (f := fun k => mVal PV S44K.N S44K.T (HexaM.T k)) k hk
      rw [hs] at e
      exact e)
  have all4 : ∀ {p : Nat → Bool}, (∀ k < HexaM.N, p k = true) → allN HexaM.N p = true := fun h => by
    rw [allN_eq', List.all_eq_true]
    exact fun k hk => h k (List.mem_range.1 hk)
  have hA : (allN HexaM.N fun k => strictB (HexaM.T k) fun m =>
      CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (fix16 m)) (inV0 PV m)) = true :=
    all4 fun k hk => by rw [strictB_eqV]; exact (sp k hk).1
  have hB : (allN HexaM.N fun k => strictB (HexaM.T k) fun m =>
      CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (CFSG.KLie.CT.andB (normV0 PV m) (inV0 PV (pw 64 7 m 9))))
        (inL S44K.N S44K.T m)) = true :=
    all4 fun k hk => by rw [strictB_eqV]; exact (sp k hk).2.1
  have hC : (allN HexaM.N fun k => strictB (HexaM.T k) fun m =>
      CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (normV0 PV m))
        (allN 16 fun v => Nat.blt (pg 7 (mask 7) m v) 16)) = true :=
    all4 fun k hk => by rw [strictB_eqV]; exact (sp k hk).2.2.1
  have hD : (allN HexaM.N fun k => strictB (HexaM.T k) fun m =>
      CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (CFSG.KLie.CT.andB (normV0 PV m) (sixTriv PV m)))
        (inV0 PV m)) = true :=
    all4 fun k hk => by rw [strictB_eqV]; exact (sp k hk).2.2.2.1
  have hN : normCount PV HexaM.N HexaM.T = 144 := by
    rw [← hs]
    exact sumN_congrV fun k hk => ((sp k hk).2.2.2.2).symm
  unfold v0K
  rw [hA, hB, hC, hD, hN]
  quickRfl

theorem kTau : tauChk PV Om Mu MP NFP = true := by quickRfl

@[expose] noncomputable def homGK (PV : Nat → Nat) (f : Nat) : Bool :=
  allN 256 fun i => allN 8 fun k =>
    Nat.beq (pg 9 (mask 9) f (starK PV i (Nat.pow 2 k)))
      (starK PV (pg 9 (mask 9) f i) (pg 9 (mask 9) f (Nat.pow 2 k)))

@[expose] noncomputable def sel4K (a1 a2 a3 : Nat) (d : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq c 0, nat_lit 0,
    nIf(Nat.beq c 1, a1, nIf(Nat.beq c 2, a2, nIf(Nat.beq c 3, a3, d c))))

@[expose] noncomputable def compB (Om Mu : Nat) (MP : Nat → Nat) (s1 s2 d : Nat × Nat) (y : Nat)
    (k : (Nat → Nat) → Nat) : Nat :=
  strictN (compK Om Mu MP s1 s2 d y 1) fun a1 => strictN (compK Om Mu MP s1 s2 d y 2) fun a2 =>
    strictN (compK Om Mu MP s1 s2 d y 3) fun a3 => k (sel4K a1 a2 a3 (compK Om Mu MP s1 s2 d y))

@[expose] noncomputable def candBK (PV : Nat → Nat) (Om Mu : Nat) (MP : Nat → Nat) (NF : Nat)
    (s1 s2 : Nat × Nat) (y0 y1 y2 y3 : Nat) : Nat :=
  compB Om Mu MP s1 s2 (0, 1) y0 fun c0 => compB Om Mu MP s1 s2 (1, 0) y1 fun c1 =>
    compB Om Mu MP s1 s2 (0, 1) y2 fun c2 => compB Om Mu MP s1 s2 (0, 1) y3 fun c3 =>
      pmk 256 9 fun i =>
        starK PV (starK PV (starK PV (c0 (nfK NF (4 * i))) (c1 (nfK NF (4 * i + 1))))
          (c2 (nfK NF (4 * i + 2)))) (c3 (nfK NF (4 * i + 3)))

theorem sel4K_eq (a : Nat → Nat) (c : Nat) :
    sel4K (a 1) (a 2) (a 3) a c = nIf(Nat.beq c 0, nat_lit 0, a c) := by
  rcases c with _ | _ | _ | _ | c <;> rfl

theorem compB_eq (Om Mu : Nat) (MP : Nat → Nat) (s1 s2 d : Nat × Nat) (y : Nat)
    (k : (Nat → Nat) → Nat) : compB Om Mu MP s1 s2 d y k = k (compK Om Mu MP s1 s2 d y) := by
  unfold compB
  rw [strictN_eq', strictN_eq', strictN_eq']
  congr 1
  funext c
  rw [sel4K_eq (compK Om Mu MP s1 s2 d y) c]
  rcases c with _ | c <;> rfl

theorem candBK_eq (PV : Nat → Nat) (Om Mu : Nat) (MP : Nat → Nat) (NF : Nat)
    (s1 s2 : Nat × Nat) (y0 y1 y2 y3 : Nat) :
    candBK PV Om Mu MP NF s1 s2 y0 y1 y2 y3 = candK PV Om Mu MP NF s1 s2 y0 y1 y2 y3 := by
  unfold candBK
  rw [compB_eq, compB_eq, compB_eq, compB_eq]
  rfl

@[expose] noncomputable def autGK (PV : Nat → Nat) (Om Mu : Nat) (MP : Nat → Nat) (NF NN : Nat)
    (TN : Nat → Nat) (lo len : Nat) : Bool :=
  allR (fun k => (fun s : (Nat × Nat) × (Nat × Nat) =>
    (fixK Om Mu MP s.1 s.2 (1, 0)).all fun y0 => (fixK Om Mu MP s.1 s.2 (0, 1)).all fun y1 =>
      (fixK Om Mu MP s.1 s.2 (1, 1)).all fun y2 => (fixK Om Mu MP s.1 s.2 (1, 2)).all fun y3 =>
        strictB (candBK PV Om Mu MP NF s.1 s.2 y0 y1 y2 y3) fun f =>
          CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (homGK PV f)) (inL NN TN f))
    (smSigmas.getD k ((0, 0), (0, 0)))) lo len

theorem homGK_of {P : Nat → Nat} {f : Nat} (h : homK P f = true) : homGK P f = true := by
  unfold homK at h
  unfold homGK
  rw [allN_eq', List.all_eq_true] at h ⊢
  intro i hi
  have hi' := h i hi
  rw [allN_eq', List.all_eq_true] at hi' ⊢
  intro k hk
  have hk' := List.mem_range.1 hk
  have h2 : Nat.pow 2 k < 256 := by interval_cases k <;> decide
  exact hi' (Nat.pow 2 k) (List.mem_range.2 h2)

theorem allR_mono {f g : Nat → Bool} (lo : Nat) (h : ∀ k, f k = true → g k = true) :
    ∀ len, allR f lo len = true → allR g lo len = true
  | 0, _ => rfl
  | n + 1, hf => by
    have e : ∀ f : Nat → Bool, allR f lo (n + 1) = (allR f lo n && f (lo + n)) := fun f => by
      change CFSG.KLie.CT.andB (allR f lo n) (f (Nat.add lo n)) = _
      generalize allR f lo n = b
      cases b <;> rfl
    rw [e] at hf ⊢
    rw [Bool.and_eq_true] at hf ⊢
    exact ⟨allR_mono lo h n hf.1, h _ hf.2⟩

theorem autK_of_autGK {lo len : Nat} (h : autGK PV Om Mu MP NFP S44N.N S44N.T lo len = true) :
    autK PV Om Mu MP NFP S44N.N S44N.T lo len = true := by
  refine allR_mono lo (fun k hk => ?_) len h
  simp only [List.all_eq_true] at hk ⊢
  intro y0 h0 y1 h1 y2 h2 y3 h3
  have e := hk y0 h0 y1 h1 y2 h2 y3 h3
  rw [strictB_eq', orB_eq, notB_eq, candBK_eq] at e
  rw [strictB_eq', orB_eq, notB_eq]
  rcases hh : homK PV (candK PV Om Mu MP NFP _ _ y0 y1 y2 y3) with _ | _
  · rfl
  · rw [homGK_of hh] at e
    exact e

@[expose] noncomputable def preK (PV : Nat → Nat) (F : Nat → Nat) : Bool :=
  allN 8 fun a => allN 8 fun k =>
    Nat.beq (F (starK PV (Nat.pow 2 a) (Nat.pow 2 k))) (starK PV (F (Nat.pow 2 a)) (F (Nat.pow 2 k)))

@[expose] noncomputable def compBB (Om Mu : Nat) (MP : Nat → Nat) (s1 s2 d : Nat × Nat) (y : Nat)
    (k : (Nat → Nat) → Bool) : Bool :=
  strictB (compK Om Mu MP s1 s2 d y 1) fun a1 => strictB (compK Om Mu MP s1 s2 d y 2) fun a2 =>
    strictB (compK Om Mu MP s1 s2 d y 3) fun a3 => k (sel4K a1 a2 a3 (compK Om Mu MP s1 s2 d y))

@[expose] noncomputable def candTB (PV : Nat → Nat) (Om Mu : Nat) (MP : Nat → Nat) (NF : Nat)
    (s1 s2 : Nat × Nat) (y0 y1 y2 y3 : Nat) (k : (Nat → Nat) → Bool) : Bool :=
  compBB Om Mu MP s1 s2 (0, 1) y0 fun c0 => compBB Om Mu MP s1 s2 (1, 0) y1 fun c1 =>
    compBB Om Mu MP s1 s2 (0, 1) y2 fun c2 => compBB Om Mu MP s1 s2 (0, 1) y3 fun c3 =>
      k fun i => starK PV (starK PV (starK PV (c0 (nfK NF (4 * i))) (c1 (nfK NF (4 * i + 1))))
          (c2 (nfK NF (4 * i + 2)))) (c3 (nfK NF (4 * i + 3)))

@[expose] noncomputable def autPK (PV : Nat → Nat) (Om Mu : Nat) (MP : Nat → Nat) (NF NN : Nat)
    (TN : Nat → Nat) (lo len : Nat) : Bool :=
  allR (fun k => (fun s : (Nat × Nat) × (Nat × Nat) =>
    (fixK Om Mu MP s.1 s.2 (1, 0)).all fun y0 => (fixK Om Mu MP s.1 s.2 (0, 1)).all fun y1 =>
      (fixK Om Mu MP s.1 s.2 (1, 1)).all fun y2 => (fixK Om Mu MP s.1 s.2 (1, 2)).all fun y3 =>
        candTB PV Om Mu MP NF s.1 s.2 y0 y1 y2 y3 fun F =>
          CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (preK PV F)) (strictB (pmk 256 9 F) fun f =>
            CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (homGK PV f)) (inL NN TN f)))
    (smSigmas.getD k ((0, 0), (0, 0)))) lo len

theorem compBB_eq (Om Mu : Nat) (MP : Nat → Nat) (s1 s2 d : Nat × Nat) (y : Nat)
    (k : (Nat → Nat) → Bool) : compBB Om Mu MP s1 s2 d y k = k (compK Om Mu MP s1 s2 d y) := by
  unfold compBB
  rw [strictB_eqV, strictB_eqV, strictB_eqV]
  congr 1
  funext c
  rw [sel4K_eq (compK Om Mu MP s1 s2 d y) c]
  rcases c with _ | c <;> rfl

theorem candTB_eq (PV : Nat → Nat) (Om Mu : Nat) (MP : Nat → Nat) (NF : Nat)
    (s1 s2 : Nat × Nat) (y0 y1 y2 y3 : Nat) (k : (Nat → Nat) → Bool) :
    candTB PV Om Mu MP NF s1 s2 y0 y1 y2 y3 k =
      k fun i => candAtK PV Om Mu MP NF s1 s2 y0 y1 y2 y3 i := by
  unfold candTB
  rw [compBB_eq, compBB_eq, compBB_eq, compBB_eq]
  rfl

theorem preK_of_homGK {PV : Nat → Nat} (hPV : ∀ i < 4, PP 64 7 (PV i)) {F : Nat → Nat}
    (hF : ∀ x < 256, F x < 2 ^ 9) (h : homGK PV (pmk 256 9 F) = true) : preK PV F = true := by
  unfold homGK at h
  unfold preK
  rw [allN_eq', List.all_eq_true] at h ⊢
  intro a ha
  have ha' := List.mem_range.1 ha
  have h2 : Nat.pow 2 a < 256 := by interval_cases a <;> decide
  have h1 := h (Nat.pow 2 a) (List.mem_range.2 h2)
  rw [allN_eq', List.all_eq_true] at h1 ⊢
  intro k hk
  have hk' := List.mem_range.1 hk
  have h3 : Nat.pow 2 k < 256 := by interval_cases k <;> decide
  have e := h1 k hk
  rwa [CFSG.KC.HexaStabK.pg_pmk (by decide) hF (CFSG.KC.Step44K.starK_lt hPV h2 h3),
    CFSG.KC.HexaStabK.pg_pmk (by decide) hF h2, CFSG.KC.HexaStabK.pg_pmk (by decide) hF h3] at e

theorem candAt_lt (hPV : ∀ i < 4, PP 64 7 (PV i)) (po : PP 64 7 Om) (pm : PP 64 7 Mu)
    (hMP : ∀ i < 4, MP i < 4) (s1 s2 : Nat × Nat) {y0 y1 y2 y3 : Nat} (hy0 : y0 < 256)
    (hy1 : y1 < 256) (hy2 : y2 < 256) (hy3 : y3 < 256) (i : Nat) :
    candAtK PV Om Mu MP NFP s1 s2 y0 y1 y2 y3 i < 256 := by
  have c0 := CFSG.KC.Step44K.comp_lt po pm hMP hy0 s1 s2 (0, 1) (nfK NFP (4 * i))
  have c1 := CFSG.KC.Step44K.comp_lt po pm hMP hy1 s1 s2 (1, 0) (nfK NFP (4 * i + 1))
  have c2 := CFSG.KC.Step44K.comp_lt po pm hMP hy2 s1 s2 (0, 1) (nfK NFP (4 * i + 2))
  have c3 := CFSG.KC.Step44K.comp_lt po pm hMP hy3 s1 s2 (0, 1) (nfK NFP (4 * i + 3))
  exact CFSG.KC.Step44K.starK_lt hPV (CFSG.KC.Step44K.starK_lt hPV (CFSG.KC.Step44K.starK_lt hPV c0 c1) c2) c3

theorem fixK_lt (po : PP 64 7 Om) (pm : PP 64 7 Mu) (hMP : ∀ i < 4, MP i < 4)
    {s1 s2 k : Nat × Nat} {y : Nat} (h : y ∈ fixK Om Mu MP s1 s2 k) : y < 256 := by
  rw [CFSG.KC.Step44K.fixK_eq (muPi := hexaMuPi) (MP := MP) po pm (fun _ _ => rfl) hMP] at h
  exact List.mem_range.1 (List.mem_filter.1 h).1

theorem autGK_of_autPK (hPV : ∀ i < 4, PP 64 7 (PV i)) (po : PP 64 7 Om) (pm : PP 64 7 Mu)
    (hMP : ∀ i < 4, MP i < 4) {lo len : Nat}
    (h : autPK PV Om Mu MP NFP S44N.N S44N.T lo len = true) :
    autGK PV Om Mu MP NFP S44N.N S44N.T lo len = true := by
  refine allR_mono lo (fun k hk => ?_) len h
  simp only [List.all_eq_true] at hk ⊢
  intro y0 h0 y1 h1 y2 h2 y3 h3
  have e := hk y0 h0 y1 h1 y2 h2 y3 h3
  simp only [candTB_eq] at e
  rw [orB_eq, notB_eq] at e
  rw [candBK_eq]
  unfold candK
  have hF : ∀ x < 256, candAtK PV Om Mu MP NFP (smSigmas.getD k ((0, 0), (0, 0))).1
      (smSigmas.getD k ((0, 0), (0, 0))).2 y0 y1 y2 y3 x < 2 ^ 9 := fun x _ =>
    Nat.lt_trans (candAt_lt hPV po pm hMP _ _ (fixK_lt po pm hMP h0) (fixK_lt po pm hMP h1)
      (fixK_lt po pm hMP h2) (fixK_lt po pm hMP h3) x) (by decide)
  cases hp : preK PV fun i => candAtK PV Om Mu MP NFP (smSigmas.getD k ((0, 0), (0, 0))).1
      (smSigmas.getD k ((0, 0), (0, 0))).2 y0 y1 y2 y3 i
  · have hg : homGK PV (pmk 256 9 fun i => candAtK PV Om Mu MP NFP
        (smSigmas.getD k ((0, 0), (0, 0))).1 (smSigmas.getD k ((0, 0), (0, 0))).2
        y0 y1 y2 y3 i) = false := by
      cases hh : homGK PV (pmk 256 9 fun i => candAtK PV Om Mu MP NFP
          (smSigmas.getD k ((0, 0), (0, 0))).1 (smSigmas.getD k ((0, 0), (0, 0))).2
          y0 y1 y2 y3 i)
      · rfl
      · rw [preK_of_homGK hPV hF hh] at hp
        exact absurd hp (by decide)
    rw [strictB_eqV, hg]
    rfl
  · rw [hp, Bool.not_true, Bool.false_or] at e
    exact e

@[expose] noncomputable def aB (b : Nat) : Bool := autPK PV Om Mu MP NFP S44N.N S44N.T (3 * b) 3

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

theorem autPK_add (lo a b : Nat) : autPK PV Om Mu MP NFP S44N.N S44N.T lo (a + b) =
    (autPK PV Om Mu MP NFP S44N.N S44N.T lo a && autPK PV Om Mu MP NFP S44N.N S44N.T (lo + a) b) :=
  allR_add _ lo a b

theorem autPK_join : ∀ m, (∀ b < m, aB b = true) →
    autPK PV Om Mu MP NFP S44N.N S44N.T 0 (3 * m) = true
  | 0, _ => rfl
  | m + 1, h => by
    rw [Nat.mul_succ, autPK_add, Nat.zero_add, autPK_join m (fun b hb => h b (by omega)),
      Bool.true_and]
    exact h m (by omega)

theorem kMP : (allN 4 fun i => Nat.blt (MP i) 4) = true := by quickRfl

theorem kAut : autK PV Om Mu MP NFP S44N.N S44N.T 0 48 = true :=
  have hsz : szOK 64 7 = true := by decide
  have ko := kOmMu
  autK_of_autGK <| autGK_of_autPK hPVf
    (PP_of_permOK hsz (by simp only [Bool.and_eq_true] at ko; exact ko.1.1.2))
    (PP_of_permOK hsz (by simp only [Bool.and_eq_true] at ko; exact ko.1.2))
    (fun i hi => Nat.blt_eq.mp (allN_spec kMP i hi)) <| autPK_join 16 (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ
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
