module

public import Certificates.Data.NT44Model
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.SchreierChainData
import Certificates.Kernel.NT44.BindEq
import Certificates.Kernel.NT44.BindTr
import Certificates.Kernel.NT44.Inv
import Certificates.Kernel.NT44.Words
import Certificates.Kernel.NT44.Sig
import Certificates.Kernel.NT44.Trans0
import Certificates.Kernel.NT44.Trans1
import Certificates.Kernel.NT44.Trans2
import Certificates.Kernel.NT44.Trans3
import Certificates.Kernel.NT44.ChainK
import Certificates.Kernel.NT44.ChainP
import Certificates.Kernel.NT44.Restrict
import Certificates.Kernel.NT44.PtsPos
import CFSG.Certificates.Kernel.Misc.ConjTree
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Misc.RowsBind
import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.Enum.ZCSound
import CFSG.Certificates.Kernel.LocalQTCovTPrim
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

set_option maxRecDepth 400000
set_option quotPrecheck false

namespace CertificateChecks.KernelNT44.Glue

open CFSG.GH74.GLS.NT44.PermutationNative CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2 (Rep rep_compA eqA_iff allLt_iff)
open CFSG.KC.Enum (pg pcomp permOK pidn)
open CFSG.KS (mask)
open CFSG.KS.Raw (unpack Binds)
open CFSG.KS.Raw.Orb (PRep prep_pcomp rep_unpack unpack_get)
open CFSG.KC.Misc.ConjTab (cj3 sigAt transAt sepAt parentAt)
open CFSG.KC.Misc.ConjTree (wv rep_wordA_wv wv_revneg conj_parent rawChainOK_congrW)
open CFSG.KC.Misc.ArrEnum (allNP_iff arrBind_sound rowsBind_arr)
open CFSG.KC.Misc.Clos (allR allR_iff)
open CertificateChecks.KernelNT44

local notation "nKI" => (ks ()).map (invCand 2688)
local notation "nPI" => (p0 ()).map (invCand 2688)
local notation "nLI" => (lifts ()).map (invCand 2688)
local notation "nB" => (ag ()).map fun i => (lifts ())[i]!
local notation "nBI" => (ag ()).map fun i => ((lifts ()).map (invCand 2688))[i]!
local notation "nV" => (fwd ()).map fun w => wordA 2688 (ks ()) ((ks ()).map (invCand 2688)) w
local notation "nVI" => ((fwd ()).map fun w => wordA 2688 (ks ()) ((ks ()).map (invCand 2688)) w).map
  (invCand 2688)
local notation "nOK" => (sk ()).extract 0 2
local notation "nOP" => (sp ()).extract 0 9
local notation "nU" => (parent ()).map fun w => wordA 2688 ((ag ()).map fun i => (lifts ())[i]!)
  ((ag ()).map fun i => ((lifts ()).map (invCand 2688))[i]!) w
local notation "nUI" => (parent ()).map fun w => wordA 2688 ((ag ()).map fun i => (lifts ())[i]!)
  ((ag ()).map fun i => ((lifts ()).map (invCand 2688))[i]!) (w.reverse.map fun l => -l)
local notation "nSG" => (Array.ofFn (n := 256) fun i => Array.ofFn (n := 2) fun j =>
  compA 2688 (compA 2688 (lifts ())[i.val]! (ks ())[j.val]!)
    ((lifts ()).map (invCand 2688))[i.val]! : Array (Array (Array Nat)))
local notation "𝔖" => Equiv.Perm (Fin 2688)

theorem bridgeCheck_eq (rels : List (List ℤ)) (z : List ℤ) : bridgeCheck rels z =
    if shapeOK (inputs ()) then
      (allLt 2 (fun i => isInvA 2688 (ks ())[i]! (nKI)[i]!) &&
        allLt 9 (fun i => isInvA 2688 (p0 ())[i]! (nPI)[i]!) &&
        allLt 256 (fun i => isInvA 2688 (lifts ())[i]! (nLI)[i]!) &&
        coverCheck rels z (inputs ()) nV nVI (idA 2688) &&
        restrictionCheck (inputs ()) nOK nOP nKI &&
        normalizerCheck (inputs ()) nKI nB nBI &&
        parentCheck (inputs ()) nLI nU nUI &&
        transitionCheck (inputs ()) nLI nSG &&
        innerCheck (inputs ()) nPI nSG)
    else false := rfl

theorem i_ks : (inputs ()).ks = ks () := rfl
theorem i_p0 : (inputs ()).p0 = p0 () := rfl
theorem i_lifts : (inputs ()).lifts = lifts () := rfl
theorem i_sk : (inputs ()).sk = sk () := rfl
theorem i_sp : (inputs ()).sp = sp () := rfl
theorem i_pts : (inputs ()).pts = pts () := rfl
theorem i_bk : (inputs ()).bk = bk () := rfl
theorem i_bp : (inputs ()).bp = bp () := rfl
theorem i_ag : (inputs ()).ag = ag () := rfl
theorem i_inn : (inputs ()).inn = inn () := rfl
theorem i_rev : (inputs ()).rev = rev () := rfl
theorem i_wk : (inputs ()).wk = wk () := rfl
theorem i_wp : (inputs ()).wp = wp () := rfl
theorem i_parent : (inputs ()).parent = parent () := rfl
theorem i_pw : (inputs ()).pw = pw () := rfl
theorem i_tr : (inputs ()).tr = tr () := rfl
theorem i_nw : (inputs ()).nw = nw () := rfl

theorem arr_get {α : Type} [Inhabited α] {N i : ℕ} (f : ℕ → α) (h : i < N) :
    ((List.range N).map f).toArray[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using h)]
  simp

theorem map_get {α β : Type} [Inhabited α] [Inhabited β] {a : Array α} (f : α → β) {i : ℕ}
    (h : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using h), getElem!_pos a i h, Array.getElem_map]

theorem ofFn_get {α : Type} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem extract_get {α : Type} [Inhabited α] {a : Array α} {k i : ℕ} (hi : i < k)
    (hk : k ≤ a.size) : (a.extract 0 k)[i]! = a[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos a i (by omega), Array.getElem_extract]
  simp

theorem pg8_lt (P k : ℕ) : pg 8 (mask 8) P k < 256 := by
  unfold pg
  have h1 : Nat.land (Nat.shiftRight P (Nat.mul 8 k)) (mask 8) ≤ mask 8 := Nat.and_le_right
  have h2 : mask 8 = 255 := by decide
  omega

theorem eqA_self (t : Array ℕ) : eqA 2688 t t = true :=
  allLt_iff.2 fun _ _ => beq_self_eq_true _

theorem szOK12 : CFSG.KS.Raw.szOK 2688 12 = true := by quickRfl

theorem idA12 : idA 2688 = unpack 2688 12 (pidn 2688 12) := CFSG.KC.BfsPin.idA_eq szOK12

open scoped Classical in
noncomputable def pOf (P : ℕ) : 𝔖 := if h : ∃ g, PRep 2688 12 P g then h.choose else 1

theorem prep_unique {P : ℕ} {g h : 𝔖} (hg : PRep 2688 12 P g) (hh : PRep 2688 12 P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem perm_of {P Q : ℕ} (h : permOK 2688 12 (mask 12) (2688 * 12) P Q = true) :
    PRep 2688 12 P (pOf P) ∧ PRep 2688 12 Q (pOf P)⁻¹ := by
  obtain ⟨g, hg, hq⟩ := CFSG.KC.EnumSound.permOK_perm h
  have hex : ∃ g, PRep 2688 12 P g := ⟨g, hg⟩
  have e : pOf P = g := by
    rw [pOf, dif_pos hex]
    exact prep_unique hex.choose_spec hg
  rw [e]
  exact ⟨hg, hq⟩

theorem prep_cj3 {a b c : ℕ} {α β γ : 𝔖} (ha : PRep 2688 12 a α) (hb : PRep 2688 12 b β)
    (hc : PRep 2688 12 c γ) : PRep 2688 12 (cj3 2688 12 a b c) (α * β * γ) :=
  prep_pcomp (by norm_num) (prep_pcomp (by norm_num) ha hb) hc

theorem rep_of {t : Array ℕ} {P : ℕ} {g : 𝔖} (ht : t = unpack 2688 12 P)
    (h : PRep 2688 12 P g) : Rep 2688 t g := by
  rw [ht]
  exact rep_unpack h

def FamOK (A : Array (Array ℕ)) (P Q i : ℕ) : Prop :=
  A[i]! = unpack 2688 12 P ∧ (A.map (invCand 2688))[i]! = unpack 2688 12 Q ∧
    Rep 2688 A[i]! (pOf P) ∧ Rep 2688 (A.map (invCand 2688))[i]! (pOf P)⁻¹ ∧
    isInvA 2688 A[i]! (A.map (invCand 2688))[i]! = true

theorem fam {N : ℕ} {A : Array (Array ℕ)} {P Q : ℕ → ℕ}
    (hA : A = ((List.range N).map fun i => unpack 2688 12 (P i)).toArray)
    (hp : ∀ i < N, permOK 2688 12 (mask 12) (2688 * 12) (P i) (Q i) = true) {i : ℕ}
    (hi : i < N) : FamOK A (P i) (Q i) i := by
  have h1 : A[i]! = unpack 2688 12 (P i) := by rw [hA, arr_get _ hi]
  have hs : i < A.size := by
    rw [hA]
    simpa using hi
  have h2 : (A.map (invCand 2688))[i]! = unpack 2688 12 (Q i) := by
    rw [map_get _ hs, h1, CFSG.KC.LQT.Cov.T.invCand_unpack (hp i hi)]
  obtain ⟨r1, r2⟩ := perm_of (hp i hi)
  refine ⟨h1, h2, rep_of h1 r1, rep_of h2 r2, ?_⟩
  rw [h1, h2]
  exact CFSG.KS.Raw.Orb.isInvA_unpack (hp i hi)

theorem inv_ks : ∀ i < 2, permOK 2688 12 (mask 12) (2688 * 12) (nt44KS i) (nt44KSI i) = true :=
  fun i hi => allNP_iff.1 nt44_inv_ks i hi

theorem inv_p0 : ∀ i < 9, permOK 2688 12 (mask 12) (2688 * 12) (nt44P0 i) (nt44P0I i) = true :=
  fun i hi => allNP_iff.1 nt44_inv_p0 i hi

theorem inv_l : ∀ i < 256, permOK 2688 12 (mask 12) (2688 * 12) (nt44L i) (nt44LI i) = true := by
  intro i hi
  rcases (by omega : i < 64 ∨ (64 ≤ i ∧ i < 128) ∨ (128 ≤ i ∧ i < 192) ∨ 192 ≤ i) with
    h | h | h | h
  · exact (allR_iff _ _ _).1 nt44_inv_l0 i (by omega) (by omega)
  · exact (allR_iff _ _ _).1 nt44_inv_l1 i (by omega) (by omega)
  · exact (allR_iff _ _ _).1 nt44_inv_l2 i (by omega) (by omega)
  · exact (allR_iff _ _ _).1 nt44_inv_l3 i (by omega) (by omega)

theorem ksF {i : ℕ} (hi : i < 2) : FamOK (ks ()) (nt44KS i) (nt44KSI i) i :=
  fam nt44_ks_eq inv_ks hi

theorem p0F {i : ℕ} (hi : i < 9) : FamOK (p0 ()) (nt44P0 i) (nt44P0I i) i :=
  fam nt44_p0_eq inv_p0 hi

theorem lF {i : ℕ} (hi : i < 256) : FamOK (lifts ()) (nt44L i) (nt44LI i) i :=
  fam nt44_lifts_eq inv_l hi

noncomputable def sg (i j : ℕ) : 𝔖 := pOf (nt44L i) * pOf (nt44KS j) * (pOf (nt44L i))⁻¹

theorem of_chunks {f : ℕ → Bool} (c m : ℕ) (hc : 0 < c) (h : ∀ s < m, allR (s * c) c f = true) :
    ∀ i < m * c, f i = true := by
  intro i hi
  have h1 : i / c < m := (Nat.div_lt_iff_lt_mul hc).2 hi
  exact (allR_iff _ _ _).1 (h _ h1) i (Nat.div_mul_le_self i c) (Nat.lt_div_mul_add hc)

theorem sig_all : ∀ q < 8 * 64, sigAt 2688 12 nt44Sig nt44L nt44LI nt44KS q = true :=
  of_chunks 64 8 (by norm_num) fun s hs => by
    interval_cases s
    · exact nt44_sig0
    · exact nt44_sig1
    · exact nt44_sig2
    · exact nt44_sig3
    · exact nt44_sig4
    · exact nt44_sig5
    · exact nt44_sig6
    · exact nt44_sig7

theorem tr_all : ∀ i < 16 * 16, nt44TrAt i = true :=
  of_chunks 16 16 (by norm_num) fun s hs => by
    interval_cases s
    · exact nt44_tr0
    · exact nt44_tr1
    · exact nt44_tr2
    · exact nt44_tr3
    · exact nt44_tr4
    · exact nt44_tr5
    · exact nt44_tr6
    · exact nt44_tr7
    · exact nt44_tr8
    · exact nt44_tr9
    · exact nt44_tr10
    · exact nt44_tr11
    · exact nt44_tr12
    · exact nt44_tr13
    · exact nt44_tr14
    · exact nt44_tr15

theorem sigP {i j : ℕ} (hi : i < 256) (hj : j < 2) : PRep 2688 12 (nt44Sig (2 * i + j)) (sg i j) := by
  have h := sig_all (2 * i + j) (by omega)
  unfold sigAt at h
  rw [Nat.eq_of_beq_eq_true h]
  have e1 : Nat.div (2 * i + j) 2 = i := by
    change (2 * i + j) / 2 = i
    omega
  have e2 : Nat.mod (2 * i + j) 2 = j := by
    change (2 * i + j) % 2 = j
    omega
  rw [e1, e2]
  exact prep_cj3 (perm_of (inv_l i hi)).1 (perm_of (inv_ks j hj)).1 (perm_of (inv_l i hi)).2

theorem sg_id {j : ℕ} (hj : j < 2) : sg 0 j = pOf (nt44KS j) := by
  have p := sigP (i := 0) (by norm_num) hj
  have e : nt44Sig (2 * 0 + j) = nt44KS j := by
    rw [Nat.mul_zero, Nat.zero_add]
    exact Nat.eq_of_beq_eq_true (allNP_iff.1 nt44_sig_id j hj)
  rw [e] at p
  exact prep_unique p (perm_of (inv_ks j hj)).1

theorem trans_eq {i c j : ℕ} (hi : i < 256) (hc : c < 4) (hj : j < 2) :
    sg (pg 8 (mask 8) (nt44Tr i) c) j = pOf (nt44L i) * sg (c + 1) j * (pOf (nt44L i))⁻¹ := by
  have h := tr_all i (by omega)
  unfold nt44TrAt transAt at h
  have h' := allNP_iff.1 (allNP_iff.1 h c hc) j hj
  have e : nt44Sig (2 * pg 8 (mask 8) (nt44Tr i) c + j) =
      cj3 2688 12 (nt44L i) (nt44Sig (2 * (c + 1) + j)) (nt44LI i) := Nat.eq_of_beq_eq_true h'
  have p1 := sigP (pg8_lt (nt44Tr i) c) hj
  rw [e] at p1
  exact prep_unique p1
    (prep_cj3 (perm_of (inv_l i hi)).1 (sigP (by omega) hj) (perm_of (inv_l i hi)).2)

theorem ks_perms : CFSG.KC.Enum.allN 2
    (fun j => permOK 2688 12 (mask 12) (2688 * 12) (nt44KS j) (nt44KSI j)) = true :=
  CFSG.KS.Raw.Orb.allN_iff.2 inv_ks

theorem ksWord {wd : List ℤ} {r : ℕ}
    (h : CFSG.KS.Prim.wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44KS nt44KSI 2 wd r = true) :
    wordA 2688 (ks ()) nKI wd = unpack 2688 12 r ∧ lettersOK 2 wd = true :=
  CFSG.KS.Prim.wordEqK_sound ⟨rfl, fun _ hj => (ksF hj).1⟩ ks_perms h

theorem ks_rep : ∀ w : List ℤ, lettersOK 2 w = true →
    Rep 2688 (wordA 2688 (ks ()) nKI w) (wv (fun j => pOf (nt44KS j)) w) :=
  rep_wordA_wv (fun _ hh => (ksF hh).2.2.1) (fun _ hh => (ksF hh).2.2.2.1)

theorem vF {i : ℕ} (hi : i < 2) : (nV)[i]! = unpack 2688 12 (nt44V i) := by
  have hs : i < (fwd ()).size := by
    rw [show (fwd ()).size = 2 from rfl]
    exact hi
  rw [map_get _ hs]
  exact (ksWord (allNP_iff.1 nt44_fwd i hi)).1

theorem inv_v : ∀ i < 2, permOK 2688 12 (mask 12) (2688 * 12) (nt44V i) (nt44VI i) = true :=
  fun i hi => allNP_iff.1 nt44_inv_v i hi

theorem vIF {i : ℕ} (hi : i < 2) : (nVI)[i]! = unpack 2688 12 (nt44VI i) := by
  have hs : i < (nV).size := by
    rw [Array.size_map, show (fwd ()).size = 2 from rfl]
    exact hi
  rw [map_get _ hs, vF hi, CFSG.KC.LQT.Cov.T.invCand_unpack (inv_v i hi)]

theorem vWord {wd : List ℤ} {r : ℕ}
    (h : CFSG.KS.Prim.wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44V nt44VI 2 wd r = true) :
    wordA 2688 nV nVI wd = unpack 2688 12 r ∧ lettersOK 2 wd = true :=
  CFSG.KS.Prim.wordEqK_sound ⟨by rw [Array.size_map]; rfl, fun _ hj => vF hj⟩
    (CFSG.KS.Raw.Orb.allN_iff.2 inv_v) h

theorem invs_ks : allLt 2 (fun i => isInvA 2688 (ks ())[i]! (nKI)[i]!) = true :=
  allLt_iff.2 fun _ hi => (ksF hi).2.2.2.2

theorem invs_p0 : allLt 9 (fun i => isInvA 2688 (p0 ())[i]! (nPI)[i]!) = true :=
  allLt_iff.2 fun _ hi => (p0F hi).2.2.2.2

theorem invs_l : allLt 256 (fun i => isInvA 2688 (lifts ())[i]! (nLI)[i]!) = true :=
  allLt_iff.2 fun _ hi => (lF hi).2.2.2.2

theorem cover_ok : coverCheck (CFSG.LieType.Multipliers.L34.coverWs.map
    (List.map CFSG.Certificates.schreierLetterCode))
    (CFSG.LieType.Multipliers.L34.zThree.map CFSG.Certificates.schreierLetterCode)
    (inputs ()) nV nVI (idA 2688) = true := by
  unfold coverCheck
  simp only [i_rev, i_ks, Bool.and_eq_true]
  refine ⟨⟨⟨⟨allLt_iff.2 fun i hi => ?_, List.all_eq_true.2 fun w hw => ?_⟩, ?_⟩, ?_⟩,
    allLt_iff.2 fun i hi => ?_⟩
  · rw [vF hi, vIF hi]
    exact CFSG.KS.Raw.Orb.isInvA_unpack (inv_v i hi)
  · obtain ⟨e, hl⟩ := vWord (List.all_eq_true.1 nt44_cover w hw)
    rw [Bool.and_eq_true, e, idA12]
    exact ⟨hl, eqA_self _⟩
  · exact (vWord nt44_z).2
  · rw [(vWord nt44_z).1, idA12]
    exact eqA_self _
  · obtain ⟨e, hl⟩ := vWord (allNP_iff.1 nt44_rev i hi)
    rw [Bool.and_eq_true, e, (ksF hi).1]
    exact ⟨hl, eqA_self _⟩

theorem pts_eq : pts () = unpack 448 12 (nt44Pts 0) := arrBind_sound nt44_pts_bind

theorem pos_facts {x : ℕ} (hx : x < 448) : pg 12 (mask 12) (nt44Pts 0) x < 2688 ∧
    pg 9 (mask 9) (nt44Pos 0) (pg 12 (mask 12) (nt44Pts 0) x) = x := by
  have h := allNP_iff.1 nt44_pos x hx
  simp only [posAt, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem skF {i : ℕ} (hi : i < 7) : (sk ())[i]! = unpack 448 9 (nt44SK i) := by
  rw [nt44_sk_eq, arr_get _ hi]

theorem spF {i : ℕ} (hi : i < 10) : (sp ())[i]! = unpack 448 9 (nt44SP i) := by
  rw [nt44_sp_eq, arr_get _ hi]

theorem sk_perm {i : ℕ} (hi : i < 7) :
    permOK 448 9 (mask 9) (448 * 9) (nt44SK i) (CK.SI i) = true := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 CK.perm i hi
  rwa [Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 CK.bS i hi)] at h

theorem sp_perm {i : ℕ} (hi : i < 10) :
    permOK 448 9 (mask 9) (448 * 9) (nt44SP i) (CP.SI i) = true := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 CP.perm i hi
  rwa [Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 CP.bS i hi)] at h

theorem bindsK : Binds 448 9 CK.S 7 4 CK.BP (sk ()) (bk ()) :=
  ⟨by norm_num, by norm_num, by norm_num, rfl, fun j hj => by
    rw [skF hj, Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 CK.bS j hj)], rfl, CK.bget⟩

theorem bindsP : Binds 448 9 CP.S 10 3 CP.BP (sp ()) (bp ()) :=
  ⟨by norm_num, by norm_num, by norm_num, rfl, fun j hj => by
    rw [spF hj, Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 CP.bS j hj)], rfl, CP.bget⟩

theorem chainK : rawChainOK 448 nOK (sk ()) (bk ()) (wk ()) 8 = true := by
  rw [rawChainOK_congrW (W' := CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 7 nt44WkD)
    (by decide) (fun j h1 h2 => by
      have hsk : (sk ()).size = 7 := rfl
      have h1' : 2 ≤ j := by simp [hsk] at h1; omega
      have h2' : j < 7 := h2
      interval_cases j <;> rfl)]
  exact CFSG.KS.Raw.Orb.rawChainOK_of_K bindsK CK.head CK.hl CK.hNS CK.hs

theorem chainP : rawChainOK 448 nOP (sp ()) (bp ()) (wp ()) 8 = true := by
  rw [rawChainOK_congrW (W' := CFSG.Sporadic.Schreier.Co3.Native.wordsArr 9 10 nt44WpD)
    (by decide) (fun j h1 h2 => by
      have hsp : (sp ()).size = 10 := rfl
      have h1' : 9 ≤ j := by simp [hsp] at h1; omega
      have h2' : j < 10 := h2
      interval_cases j <;> rfl)]
  exact CFSG.KS.Raw.Orb.rawChainOK_of_K bindsP CP.head CP.hl CP.hNS CP.hs

theorem orbK : (rawOrbitSizes 448 (sk ()) (bk ())).prod = 322560 := by
  rw [CFSG.KS.Raw.Orb.rawOrbitSizes_of_K bindsK CK.perm CK.hl]
  exact CK.orbProd

theorem orbP : (rawOrbitSizes 448 (sp ()) (bp ())).prod = 1024 := by
  rw [CFSG.KS.Raw.Orb.rawOrbitSizes_of_K bindsP CP.perm CP.hl]
  exact CP.orbProd

theorem restr_ok : restrictionCheck (inputs ()) nOK nOP nKI = true := by
  unfold restrictionCheck
  simp only [i_pts, i_ks, i_p0, i_sk, i_sp, i_bk, i_bp, i_wk, i_wp, i_pw, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨allLt_iff.2 fun i hi => allLt_iff.2 fun x hx => ?_,
    allLt_iff.2 fun i hi => allLt_iff.2 fun x hx => ?_⟩, chainK⟩, beq_iff_eq.2 orbK⟩, chainP⟩,
    beq_iff_eq.2 orbP⟩, allLt_iff.2 fun i hi => ?_⟩
  · have h := allNP_iff.1 nt44_restr_ks i hi
    unfold restrAt at h
    have h' := Nat.eq_of_beq_eq_true (allNP_iff.1 h x hx)
    have hs := ((CFSG.KS.Raw.Orb.permOK_facts (sk_perm (i := i) (by omega))).2.2 x hx).1
    rw [extract_get (a := sk ()) hi (by decide), skF (i := i) (by omega), unpack_get hx, pts_eq,
      unpack_get hs, unpack_get hx, (ksF hi).1, unpack_get (pos_facts hx).1]
    exact beq_iff_eq.2 h'
  · have h := allNP_iff.1 nt44_restr_p0 i hi
    unfold restrAt at h
    have h' := Nat.eq_of_beq_eq_true (allNP_iff.1 h x hx)
    have hs := ((CFSG.KS.Raw.Orb.permOK_facts (sp_perm (i := i) (by omega))).2.2 x hx).1
    rw [extract_get (a := sp ()) hi (by decide), spF (i := i) (by omega), unpack_get hx, pts_eq,
      unpack_get hs, unpack_get hx, (p0F hi).1, unpack_get (pos_facts hx).1]
    exact beq_iff_eq.2 h'
  · obtain ⟨e, hl⟩ := ksWord (allNP_iff.1 nt44_pw i hi)
    rw [Bool.and_eq_true, e, (p0F hi).1]
    exact ⟨hl, eqA_self _⟩

theorem ag_get : ∀ k < 4, (ag ())[k]! = k + 1 := by
  intro k hk
  interval_cases k <;> rfl

theorem bF {k : ℕ} (hk : k < 4) : Rep 2688 (nB)[k]! (pOf (nt44L (k + 1))) ∧
    Rep 2688 (nBI)[k]! (pOf (nt44L (k + 1)))⁻¹ := by
  have hs : k < (ag ()).size := by
    rw [show (ag ()).size = 4 from rfl]
    exact hk
  rw [map_get _ hs, map_get _ hs, ag_get k hk]
  exact ⟨(lF (by omega)).2.2.1, (lF (by omega)).2.2.2.1⟩

theorem norm_word {k j : ℕ} (hk : k < 4) (hj : j < 2) :
    Rep 2688 (wordA 2688 (ks ()) nKI (nw ())[k]!.left[j]!) (sg (k + 1) j) ∧
      Rep 2688 (wordA 2688 (ks ()) nKI (nw ())[k]!.inverse[j]!)
        ((pOf (nt44L (k + 1)))⁻¹ * pOf (nt44KS j) * pOf (nt44L (k + 1))) ∧
      lettersOK 2 (nw ())[k]!.left[j]! = true := by
  have h := allNP_iff.1 (allNP_iff.1 nt44_norm k hk) j hj
  rw [Bool.and_eq_true] at h
  obtain ⟨e1, hl⟩ := ksWord h.1
  obtain ⟨e2, -⟩ := ksWord h.2
  have pl := perm_of (inv_l (k + 1) (by omega))
  have pk := (perm_of (inv_ks j hj)).1
  refine ⟨?_, ?_, hl⟩
  · rw [e1]
    exact rep_unpack (prep_cj3 pl.1 pk pl.2)
  · rw [e2]
    exact rep_unpack (prep_cj3 pl.2 pk pl.1)

theorem norm_ok : normalizerCheck (inputs ()) nKI nB nBI = true := by
  unfold normalizerCheck
  simp only [i_ks, i_nw]
  refine allLt_iff.2 fun k hk => allLt_iff.2 fun j hj => ?_
  obtain ⟨r1, r2, -⟩ := norm_word hk hj
  have rk := (ksF hj).2.2.1
  rw [Bool.and_eq_true]
  exact ⟨(eqA_iff r1 (rep_compA (rep_compA (bF hk).1 rk) (bF hk).2)).2 rfl,
    (eqA_iff r2 (rep_compA (rep_compA (bF hk).2 rk) (bF hk).1)).2 rfl⟩

theorem sgR {i j : ℕ} (hi : i < 256) (hj : j < 2) : Rep 2688 ((nSG)[i]!)[j]! (sg i j) := by
  rw [ofFn_get _ hi]
  beta_reduce
  rw [ofFn_get _ hj]
  exact rep_compA (rep_compA (lF hi).2.2.1 (ksF hj).2.2.1) (lF hi).2.2.2.1

theorem sgv {i x : ℕ} (hi : i < 256) (hx : x < 2688) :
    (((nSG)[i]!)[0]!)[x]! = pg 12 (mask 12) (nt44Sig (2 * i)) x := by
  rw [(sgR (j := 0) hi (by norm_num)).apply hx]
  exact (sigP (j := 0) hi (by norm_num) ⟨x, hx⟩).symm

theorem tr_size : (tr ()).size = 256 := by
  simp only [tr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil]

theorem tr_eq : tr () = ((List.range 256).map fun i => unpack 4 8 (nt44Tr i)).toArray :=
  rowsBind_arr tr_size nt44_tr_bind

theorem tr_get {i k : ℕ} (hi : i < 256) (hk : k < 4) :
    ((tr ())[i]!)[k]! = pg 8 (mask 8) (nt44Tr i) k := by
  rw [tr_eq, arr_get _ hi, unpack_get hk]

theorem sep_all : ∀ i < 256, sepAt 2688 12 nt44Sig 0 217 i = true :=
  fun i hi => (allR_iff _ _ _).1 nt44_sep i (Nat.zero_le i) (by omega)

theorem trans_ok : transitionCheck (inputs ()) nLI nSG = true := by
  unfold transitionCheck
  simp only [i_ks, i_tr, i_ag, i_lifts, Bool.and_eq_true]
  refine ⟨⟨allLt_iff.2 fun j hj => ?_, allLt_iff.2 fun i hi => allLt_iff.2 fun k hk =>
    allLt_iff.2 fun j hj => ?_⟩, allLt_iff.2 fun i hi => allLt_iff.2 fun j hj => ?_⟩
  · exact (eqA_iff (sgR (i := 0) (by norm_num) hj) (ksF hj).2.2.1).2 (sg_id hj)
  · rw [tr_get hi hk, ag_get k hk]
    exact (eqA_iff (sgR (pg8_lt _ _) hj)
      (rep_compA (rep_compA (lF hi).2.2.1 (sgR (i := k + 1) (by omega) hj)) (lF hi).2.2.2.1)).2
      (trans_eq hi hk hj)
  · by_cases hij : i < j
    · have h := sep_all j hj
      unfold sepAt at h
      have hs := allNP_iff.1 h i hij
      simp only [Nat.mul_eq] at hs
      rw [sgv (x := 0) hi (by norm_num), sgv (x := 0) hj (by norm_num),
        sgv (x := 217) hi (by norm_num), sgv (x := 217) hj (by norm_num)]
      by_cases e1 : pg 12 (mask 12) (nt44Sig (2 * i)) 0 = pg 12 (mask 12) (nt44Sig (2 * j)) 0
      · by_cases e2 : pg 12 (mask 12) (nt44Sig (2 * i)) 217 =
            pg 12 (mask 12) (nt44Sig (2 * j)) 217
        · rw [e1, e2, Nat.beq_refl, Nat.beq_refl] at hs
          exact absurd hs (by decide)
        · simp [e2]
      · simp [e1]
    · simp [hij]

theorem inn_lt : ∀ i < 9, (inn ())[i]! < 256 := by decide

theorem inner_ok : innerCheck (inputs ()) nPI nSG = true := by
  unfold innerCheck
  simp only [i_ks, i_p0, i_inn]
  refine allLt_iff.2 fun i hi => allLt_iff.2 fun j hj => ?_
  have h := Nat.eq_of_beq_eq_true (allNP_iff.1 (allNP_iff.1 nt44_inner i hi) j hj)
  have p1 := prep_cj3 (perm_of (inv_p0 i hi)).1 (perm_of (inv_ks j hj)).1
    (perm_of (inv_p0 i hi)).2
  have p2 := sigP (inn_lt i hi) hj
  have e : cj3 2688 12 (nt44P0 i) (nt44KS j) (nt44P0I i) = nt44Sig (2 * (inn ())[i]! + j) := h
  rw [e] at p1
  exact (eqA_iff (rep_compA (rep_compA (p0F hi).2.2.1 (ksF hj).2.2.1) (p0F hi).2.2.2.1)
    (sgR (inn_lt i hi) hj)).2 (prep_unique p1 p2)

theorem parent_size : (parent ()).size = 256 := by
  simp only [parent, Array.size_append, List.size_toArray, List.length_cons, List.length_nil]

theorem get_toList {a : Array (List ℤ)} {i : ℕ} (hs : i < a.size) :
    a[i]! = a.toList.getD i [] := by
  simp [hs, List.getD_eq_getElem?_getD]

theorem par_get {i : ℕ} (hi : i < 256) : (parent ())[i]! = (parent ()).toList.getD i [] :=
  get_toList (by rw [parent_size]; exact hi)

theorem parent_tree : ∀ i < 256, (∀ z ∈ (parent ()).toList.getD i [], 1 ≤ z ∧ z ≤ 4) ∧
    ∀ j < 2, wv (fun h => pOf (nt44L (h + 1))) ((parent ()).toList.getD i []) * pOf (nt44KS j) *
      (wv (fun h => pOf (nt44L (h + 1))) ((parent ()).toList.getD i []))⁻¹ = sg i j := by
  have hpar := nt44_parent
  rw [Bool.and_eq_true, decide_eq_true_eq] at hpar
  obtain ⟨h0, hR⟩ := hpar
  refine conj_parent (N := 256) (m := 2) (d := 4) (k := fun j => pOf (nt44KS j))
    (l := fun i => pOf (nt44L i))
    (par := fun i => pg 8 (mask 8) (nt44Par 0) i) (T := fun i c => pg 8 (mask 8) (nt44Tr i) c)
    h0 ?_ (fun j hj => sg_id hj) (fun i hi c hc j hj => trans_eq hi hc hj) ?_
  · intro i hi1 hi2
    have h := (allR_iff _ _ _).1 hR i hi1 (by omega)
    unfold parentAt at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hw, h1⟩, h4⟩, ht⟩ := h
    refine ⟨pg8_lt _ _, (((parent ()).toList.getD i []).getLastD 0).toNat - 1, by omega, ?_,
      Nat.eq_of_beq_eq_true ht⟩
    have e : ((((((parent ()).toList.getD i []).getLastD 0).toNat - 1 + 1 : ℕ)) : ℤ) =
        ((parent ()).toList.getD i []).getLastD 0 := by omega
    rw [e]
    exact hw
  · intro c hc j hj
    obtain ⟨r1, -, hl⟩ := norm_word hc hj
    exact ⟨_, hl, r1.unique (ks_rep _ hl)⟩

theorem letters_pos {w : List ℤ} {d : ℕ} (h : ∀ z ∈ w, 1 ≤ z ∧ z ≤ d) : lettersOK d w = true :=
  List.all_eq_true.2 fun z hz => by
    have := h z hz
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨by omega, by omega⟩

theorem letters_neg {w : List ℤ} {d : ℕ} (h : ∀ z ∈ w, 1 ≤ z ∧ z ≤ d) :
    lettersOK d (w.reverse.map fun l => -l) = true :=
  List.all_eq_true.2 fun z hz => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    have := h y (List.mem_reverse.1 hy)
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨by omega, by omega⟩

theorem parent_ok : parentCheck (inputs ()) nLI nU nUI = true := by
  unfold parentCheck
  simp only [i_ks, i_lifts]
  refine allLt_iff.2 fun i hi => allLt_iff.2 fun j hj => ?_
  obtain ⟨hz, hc⟩ := parent_tree i hi
  have hs : i < (parent ()).size := by
    rw [parent_size]
    exact hi
  have rU : Rep 2688 (nU)[i]! (wv (fun h => pOf (nt44L (h + 1)))
      ((parent ()).toList.getD i [])) := by
    rw [map_get _ hs, par_get hi]
    exact rep_wordA_wv (fun _ hh => (bF hh).1) (fun _ hh => (bF hh).2) _ (letters_pos hz)
  have rUI : Rep 2688 (nUI)[i]! (wv (fun h => pOf (nt44L (h + 1)))
      ((parent ()).toList.getD i []))⁻¹ := by
    rw [map_get _ hs, par_get hi, ← wv_revneg (fun h => pOf (nt44L (h + 1)))
      ((parent ()).toList.getD i []) fun z hz' => by have := hz z hz'; omega]
    exact rep_wordA_wv (fun _ hh => (bF hh).1) (fun _ hh => (bF hh).2) _ (letters_neg hz)
  exact (eqA_iff (rep_compA (rep_compA (lF hi).2.2.1 (ksF hj).2.2.1) (lF hi).2.2.2.1)
    (rep_compA (rep_compA rU (ksF hj).2.2.1) rUI)).2 (hc j hj).symm

theorem rowsOK_of {n w c : ℕ} {A : Array (Array ℕ)} {P Q : ℕ → ℕ}
    (hA : A = ((List.range c).map fun i => unpack n w (P i)).toArray)
    (hp : ∀ i < c, permOK n w (mask w) (n * w) (P i) (Q i) = true) : rowsOK n c A = true := by
  unfold rowsOK rowOK
  rw [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨by rw [hA]; simp, fun i hi => ?_⟩
  rw [hA, arr_get _ hi, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨by simp [unpack], fun x hx => ?_⟩
  rw [unpack_get hx]
  exact decide_eq_true ((CFSG.KS.Raw.Orb.permOK_facts (hp i hi)).2.2 x hx).1

local macro "smallK" : tactic => `(tactic| ((try simp only [allLt_iff, distinctValues,
  normalizerShapeOK, wordsLettersOK, Bool.and_eq_true]) <;> decide))

theorem shape : shapeOK (inputs ()) = true := by
  unfold shapeOK
  simp only [Bool.and_eq_true, and_assoc]
  constructorm* _ ∧ _
  · smallK
  · smallK
  · rw [i_lifts, nt44_lifts_eq]
    simp
  · exact rowsOK_of nt44_ks_eq inv_ks
  · exact rowsOK_of nt44_p0_eq inv_p0
  · exact rowsOK_of nt44_lifts_eq inv_l
  · smallK
  · rw [i_pts, allLt_iff]
    intro x hx
    rw [pts_eq, unpack_get hx]
    exact decide_eq_true (pos_facts hx).1
  · unfold distinctValues
    rw [i_pts, pts_eq, allLt_iff]
    intro i hi
    have hi' : i < 448 := by simpa [unpack] using hi
    rw [allLt_iff]
    intro j hj
    have hj' : j < 448 := by omega
    rw [unpack_get hi', unpack_get hj', bne_iff_ne, ne_eq]
    intro e
    have := (pos_facts (x := j) (by omega)).2
    rw [← e, (pos_facts hi').2] at this
    omega
  · smallK
  · smallK
  · exact rowsOK_of nt44_sk_eq fun i hi => sk_perm hi
  · exact rowsOK_of nt44_sp_eq fun i hi => sp_perm hi
  · smallK
  · smallK
  · smallK
  · smallK
  · smallK
  · smallK
  · smallK
  · rw [i_tr, beq_iff_eq]
    exact tr_size
  · rw [i_tr, allLt_iff]
    intro i hi
    rw [Bool.and_eq_true, beq_iff_eq, allLt_iff]
    refine ⟨?_, fun k hk => ?_⟩
    · rw [tr_eq, arr_get _ hi]
      simp [unpack]
    · rw [tr_get hi hk]
      exact decide_eq_true (pg8_lt _ _)
  · smallK
  · smallK
  · rw [i_parent, beq_iff_eq]
    exact parent_size
  · unfold positiveWordsOK
    rw [i_parent, parent_size, allLt_iff]
    intro i hi
    rw [par_get hi, List.all_eq_true]
    intro z hz
    have := ((parent_tree i hi).1 z hz)
    simp only [Bool.or_eq_true, beq_iff_eq]
    omega
  all_goals smallK

public theorem nt44_bridge : bridgeCheck (CFSG.LieType.Multipliers.L34.coverWs.map
    (List.map CFSG.Certificates.schreierLetterCode))
    (CFSG.LieType.Multipliers.L34.zThree.map CFSG.Certificates.schreierLetterCode) = true := by
  rw [bridgeCheck_eq, if_pos shape]
  simp only [invs_ks, invs_p0, invs_l, cover_ok, restr_ok, norm_ok, parent_ok, trans_ok, inner_ok,
    Bool.and_self]

end CertificateChecks.KernelNT44.Glue
