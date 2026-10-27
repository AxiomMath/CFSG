module

public import Certificates.Kernel.Misc.Perm.HS100.TChecks
public import Certificates.Kernel.Misc.Perm.HS100.NGlue
import CFSG.Certificates.Kernel.Spor.PackFld

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.Zassenhaus CFSG.KC.Misc.HexFlat
open CFSG.KC.Misc.ArrEnum (permB pp_of_permB memK fixK anyNP_eq)

open CFSG.KC.LQT.P (anyN)

open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.Five (eqA_F hidA pidPP and_of commA_F)

open CertificateChecks.KernelMisc.HS100.S0 (listOf any_eq cK cK_eq Z0 ppZ fixCnt_eq)

open CertificateChecks.KernelMisc.HS100.N (zasConj_unpack pZ)


theorem allN_congr {n : ℕ} {f g : ℕ → Bool} (h : ∀ i < n, f i = g i) : allN n f = allN n g := by
  apply Bool.eq_iff_iff.2
  constructor
  · intro hf
    exact CFSG.KS.PackFld.allN_of_forall fun i hi => (h i hi) ▸ allN_spec hf i hi
  · intro hg
    exact CFSG.KS.PackFld.allN_of_forall fun i hi => (h i hi).symm ▸ allN_spec hg i hi

theorem allN_range {n : ℕ} {f : ℕ → Bool} : allN n f = (List.range n).all f := by
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    exact allN_spec h i (List.mem_range.1 hi)
  · intro h
    exact CFSG.KS.PackFld.allN_of_forall fun i hi => h i (List.mem_range.2 hi)

theorem any_congr' {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.any f = l.any g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      any_congr' fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem perms' : (∀ k < 3, permB 100 7 (TX.F k) = true) ∧ (∀ k < 32, permB 100 7 (EA.F k) = true) :=
  ⟨fun k hk => allN_spec (and_of perms).1 k hk, fun k hk => allN_spec (and_of perms).2 k hk⟩

theorem nums' : TT.ng = 3 ∧ TT.N = 512 ∧ (∀ k < 3, TT.G k = TX.F k) ∧
    E0.ng = 4 ∧ E0.N = 16 ∧ E1.ng = 4 ∧ E1.N = 16 ∧ E2.ng = 4 ∧ E2.N = 16 ∧ E3.ng = 4 ∧ E3.N = 16 ∧
    E4.ng = 4 ∧ E4.N = 16 ∧ E5.ng = 4 ∧ E5.N = 16 ∧ E6.ng = 4 ∧ E6.N = 16 ∧ E7.ng = 4 ∧
    E7.N = 16 := by
  have h := nums
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩ := h
  exact ⟨h1, h2, fun k hk => Nat.eq_of_beq_eq_true (allN_spec h3 k hk), h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

theorem t_get : ∀ k < 3, zasTGens[k]! = unpack 100 7 (TX.F k) := by
  intro k hk
  rw [zasTGens, zasGens, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn, TX.eq]
  exact hexTable3_sound TX.all k hk

theorem e_get {j : ℕ} (hj : j < 8) : ∀ k < 4, (zasEGens j)[k]! = unpack 100 7 (EA.F (4 * j + k)) := by
  intro k hk
  rw [zasEGens, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn, EA.eq]
  have h32 : 4 * j + k < 32 := by omega
  exact hexTable3_sound EA.all (4 * j + k) h32

theorem z_eq : s5Z = unpack 100 7 Z0 := S0.z0_eq

theorem cZ : canonK 100 7 (mask 7) (100 * 7) Z0 = true := ppZ.1

theorem cTT : ∀ i < TT.N, canonK 100 7 (mask 7) (100 * 7) (TT.T i) = true := bfsK_canon TT.ok

theorem ppTT {i : ℕ} (hi : i < 512) : PP 100 7 (TT.T i) := pp_of_permB sz (allN_spec tperm i hi)

theorem tPin : enumOK 100 zasTGens zasTKeys zasTCert = true ∧
    zasTCert.pts = Array.ofFn (n := TT.N) fun i => unpack 100 7 (TT.T i.val) := by
  have hs : zasTGens.size = TT.ng := by rw [nums'.1]; rfl
  have hg : ∀ k < TT.ng, zasTGens[k]! = unpack 100 7 (TT.G k) := fun k hk => by
    rw [nums'.1] at hk; rw [t_get k hk, nums'.2.2.1 k hk]
  have hp : ∀ k < TT.ng, permOK 100 7 (mask 7) (100 * 7) (TT.G k)
      (pinvS 100 7 (mask 7) (TT.G k)) = true := fun k hk => by
    rw [nums'.1] at hk; rw [nums'.2.2.1 k hk]; exact perms'.1 k hk
  have hf : TT.N ≤ 2 ^ 20 := by rw [nums'.2.1]; norm_num
  exact ⟨enumOK_of_bfsK_base hs hg hp TT.ok (by decide) keys hf,
    enumBfs_pts_base hs hg TT.ok (by decide) keys hf⟩

theorem zasEC_eq {j : ℕ} (hj : j < 8) : zasEC j = zasECert j := by
  rw [zasEC, zasECerts, Array.getElem?_eq_getElem (by simpa using hj), Option.getD_some,
    Array.getElem_ofFn]

theorem ePinOf {j : ℕ} (hj : j < 8) {ng N : ℕ} {G T E S : ℕ → ℕ} (hng : ng = 4) (hN : N = 16)
    (hG : ∀ k < 4, G k = EA.F (4 * j + k)) (hk : bfsK 100 7 ng G N T E S = true) :
    enumOK 100 (zasEGens j) zasEKeys (zasEC j) = true ∧
      (zasEC j).pts = Array.ofFn (n := 16) fun i => unpack 100 7 (T i.val) := by
  subst hng hN
  have hs : (zasEGens j).size = 4 := by simp [zasEGens]
  have hg : ∀ k < 4, (zasEGens j)[k]! = unpack 100 7 (G k) := fun k hk => by
    rw [e_get hj k hk, hG k hk]
  have hp : ∀ k < 4, permOK 100 7 (mask 7) (100 * 7) (G k) (pinvS 100 7 (mask 7) (G k)) = true :=
    fun k hk => by rw [hG k hk]; exact perms'.2 _ (by omega)
  rw [zasEC_eq hj, zasECert]
  unfold zasEKeys
  exact ⟨enumOK_of_bfsK hs hg hp hk (by norm_num), enumBfs_pts hs hg hk (by norm_num)⟩

theorem ebinds' : (∀ k < 4, E0.G k = EA.F (4 * 0 + k)) ∧ (∀ k < 4, E1.G k = EA.F (4 * 1 + k)) ∧
    (∀ k < 4, E2.G k = EA.F (4 * 2 + k)) ∧ (∀ k < 4, E3.G k = EA.F (4 * 3 + k)) ∧
    (∀ k < 4, E4.G k = EA.F (4 * 4 + k)) ∧ (∀ k < 4, E5.G k = EA.F (4 * 5 + k)) ∧
    (∀ k < 4, E6.G k = EA.F (4 * 6 + k)) ∧ (∀ k < 4, E7.G k = EA.F (4 * 7 + k)) := by
  have h := ebinds
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have f := fun {g : ℕ → ℕ} {o : ℕ} (hh : allN 4 (fun k => Nat.beq (g k) (EA.F (o + k))) = true)
    (k : ℕ) (hk : k < 4) => Nat.eq_of_beq_eq_true (allN_spec hh k hk)
  refine ⟨fun k hk => ?_, fun k hk => f h1 k hk, fun k hk => f h2 k hk, fun k hk => f h3 k hk,
    fun k hk => f h4 k hk, fun k hk => f h5 k hk, fun k hk => f h6 k hk, fun k hk => f h7 k hk⟩
  rw [Nat.mul_zero, Nat.zero_add]
  exact Nat.eq_of_beq_eq_true (allN_spec h0 k hk)

theorem ePin {j : ℕ} (hj : j < 8) :
    enumOK 100 (zasEGens j) zasEKeys (zasEC j) = true ∧
      (zasEC j).pts = Array.ofFn (n := 16) (fun i => unpack 100 7 (ET j i.val)) ∧
      ∀ i < 16, canonK 100 7 (mask 7) (100 * 7) (ET j i) = true := by
  have n := nums'
  interval_cases j
  · exact ⟨(ePinOf (by norm_num) n.2.2.2.1 n.2.2.2.2.1 ebinds'.1 E0.ok).1,
      (ePinOf (by norm_num) n.2.2.2.1 n.2.2.2.2.1 ebinds'.1 E0.ok).2,
      fun i hi => bfsK_canon E0.ok i (by rw [n.2.2.2.2.1]; exact hi)⟩
  · exact ⟨(ePinOf (by norm_num) n.2.2.2.2.2.1 n.2.2.2.2.2.2.1 ebinds'.2.1 E1.ok).1,
      (ePinOf (by norm_num) n.2.2.2.2.2.1 n.2.2.2.2.2.2.1 ebinds'.2.1 E1.ok).2,
      fun i hi => bfsK_canon E1.ok i (by rw [n.2.2.2.2.2.2.1]; exact hi)⟩
  · exact ⟨(ePinOf (by norm_num) n.2.2.2.2.2.2.2.1 n.2.2.2.2.2.2.2.2.1 ebinds'.2.2.1 E2.ok).1,
      (ePinOf (by norm_num) n.2.2.2.2.2.2.2.1 n.2.2.2.2.2.2.2.2.1 ebinds'.2.2.1 E2.ok).2,
      fun i hi => bfsK_canon E2.ok i (by rw [n.2.2.2.2.2.2.2.2.1]; exact hi)⟩
  · exact ⟨(ePinOf (by norm_num) n.2.2.2.2.2.2.2.2.2.1 n.2.2.2.2.2.2.2.2.2.2.1 ebinds'.2.2.2.1
        E3.ok).1,
      (ePinOf (by norm_num) n.2.2.2.2.2.2.2.2.2.1 n.2.2.2.2.2.2.2.2.2.2.1 ebinds'.2.2.2.1 E3.ok).2,
      fun i hi => bfsK_canon E3.ok i (by rw [n.2.2.2.2.2.2.2.2.2.2.1]; exact hi)⟩
  · exact ⟨(ePinOf (by norm_num) n.2.2.2.2.2.2.2.2.2.2.2.1 n.2.2.2.2.2.2.2.2.2.2.2.2.1
        ebinds'.2.2.2.2.1 E4.ok).1,
      (ePinOf (by norm_num) n.2.2.2.2.2.2.2.2.2.2.2.1 n.2.2.2.2.2.2.2.2.2.2.2.2.1
        ebinds'.2.2.2.2.1 E4.ok).2,
      fun i hi => bfsK_canon E4.ok i (by rw [n.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hi)⟩
  · exact ⟨(ePinOf (by norm_num) n.2.2.2.2.2.2.2.2.2.2.2.2.2.1 n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        ebinds'.2.2.2.2.2.1 E5.ok).1,
      (ePinOf (by norm_num) n.2.2.2.2.2.2.2.2.2.2.2.2.2.1 n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        ebinds'.2.2.2.2.2.1 E5.ok).2,
      fun i hi => bfsK_canon E5.ok i (by rw [n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hi)⟩
  · exact ⟨(ePinOf (by norm_num) n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ebinds'.2.2.2.2.2.2.1 E6.ok).1,
      (ePinOf (by norm_num) n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ebinds'.2.2.2.2.2.2.1 E6.ok).2,
      fun i hi => bfsK_canon E6.ok i (by rw [n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hi)⟩
  · exact ⟨(ePinOf (by norm_num) n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ebinds'.2.2.2.2.2.2.2 E7.ok).1,
      (ePinOf (by norm_num) n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ebinds'.2.2.2.2.2.2.2 E7.ok).2,
      fun i hi => bfsK_canon E7.ok i (by rw [n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]; exact hi)⟩

theorem eMem {j : ℕ} (hj : j < 8) {t : ℕ} (ht : canonK 100 7 (mask 7) (100 * 7) t = true) :
    zasMem (zasEC j) (unpack 100 7 t) = memK 16 (ET j) t := by
  rw [zasMem, listOf (ePin hj).2.1]
  exact any_eq (ePin hj).2.2 ht

theorem invs' : (∀ j < 87, TTI j < 512 ∧ isInvK (TT.T (TTI j)) = true) ∧
    ∀ i < 512, isInvK (TT.T i) = true → ∃ j < 87, TTI j = i := by
  have h := invs
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, -⟩, h3⟩ := h
  refine ⟨fun j hj => ?_, fun i hi hv => ?_⟩
  · have := allN_spec h1 j hj
    simp only [Bool.and_eq_true, Nat.blt_eq] at this
    exact this
  · have := allN_spec h3 i hi
    rw [hv, Bool.not_true, Bool.false_or, anyNP_eq, List.any_eq_true] at this
    obtain ⟨j, hj, e⟩ := this
    exact ⟨j, List.mem_range.1 hj, Nat.eq_of_beq_eq_true e⟩

theorem isInv_eq {t : ℕ} (ht : canonK 100 7 (mask 7) (100 * 7) t = true) :
    zasIsInv (unpack 100 7 t) = isInvK t := by
  rw [zasIsInv, compA_unpack ht ht, hidA, eqA_F (canonK_pcomp ht ht) pidPP.1, eqA_F ht pidPP.1,
    isInvK]

theorem mem_invs {x : Array ℕ} : x ∈ zasInvs ↔ ∃ j < 87, unpack 100 7 (TT.T (TTI j)) = x := by
  rw [zasInvs, List.mem_filter, listOf tPin.2, List.mem_map]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hv⟩
    have hi' : i < 512 := by rw [← nums'.2.1]; exact List.mem_range.1 hi
    rw [isInv_eq (cTT i (by rw [nums'.2.1]; exact hi'))] at hv
    obtain ⟨j, hj, rfl⟩ := invs'.2 i hi' hv
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨h1, h2⟩ := invs'.1 j hj
    refine ⟨⟨TTI j, List.mem_range.2 (by rw [nums'.2.1]; exact h1), rfl⟩, ?_⟩
    rw [isInv_eq (cTT _ (by rw [nums'.2.1]; exact h1))]
    exact h2

theorem invs_all (g : Array ℕ → Bool) :
    zasInvs.all g = allN 87 fun j => g (unpack 100 7 (TT.T (TTI j))) := by
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true]
  constructor
  · intro h
    exact CFSG.KS.PackFld.allN_of_forall fun j hj => h _ (mem_invs.2 ⟨j, hj, rfl⟩)
  · intro h x hx
    obtain ⟨j, hj, rfl⟩ := mem_invs.1 hx
    exact allN_spec h j hj

theorem cI {j : ℕ} (hj : j < 87) : canonK 100 7 (mask 7) (100 * 7) (TT.T (TTI j)) = true :=
  cTT _ (by rw [nums'.2.1]; exact (invs'.1 j hj).1)

theorem memL2_eq {a : ℕ} (ha : canonK 100 7 (mask 7) (100 * 7) a = true) :
    zasMemL [idA 100, s5Z] (unpack 100 7 a) = (Nat.beq a (pidn 100 7) || Nat.beq a Z0) := by
  simp only [zasMemL, List.any_cons, List.any_nil, Bool.or_false]
  rw [hidA, z_eq, eqA_F ha pidPP.1, eqA_F ha cZ]

theorem comm_eq {a b : ℕ} (ha : canonK 100 7 (mask 7) (100 * 7) a = true)
    (hb : canonK 100 7 (mask 7) (100 * 7) b = true) :
    zasComm (unpack 100 7 a) (unpack 100 7 b) = cK a b := by
  rw [zasComm, compA_unpack ha hb, compA_unpack hb ha, eqA_F (canonK_pcomp ha hb) (canonK_pcomp hb ha)]
  rfl

theorem k2_eq {a b : ℕ} (ha : canonK 100 7 (mask 7) (100 * 7) a = true)
    (hb : canonK 100 7 (mask 7) (100 * 7) b = true) :
    zasMemL (zasK2 (unpack 100 7 a)) (unpack 100 7 b) = inK2 a b := by
  simp only [zasMemL, zasK2, List.any_cons, List.any_nil, Bool.or_false]
  rw [hidA, z_eq, compA_unpack cZ ha, eqA_F hb pidPP.1, eqA_F hb cZ, eqA_F hb ha,
    eqA_F hb (canonK_pcomp cZ ha), inK2]
  simp only [Bool.or_assoc]

theorem k3_eq {a b c : ℕ} (ha : canonK 100 7 (mask 7) (100 * 7) a = true)
    (hb : canonK 100 7 (mask 7) (100 * 7) b = true)
    (hc : canonK 100 7 (mask 7) (100 * 7) c = true) :
    zasMemL (zasK3 (unpack 100 7 a) (unpack 100 7 b)) (unpack 100 7 c) = inK3 a b c := by
  have e := k2_eq ha hc
  simp only [zasMemL, zasK2] at e
  simp only [zasMemL, zasK3, zasK2, List.any_append, List.map_cons, List.map_nil, List.any_cons,
    List.any_nil, Bool.or_false] at e ⊢
  rw [e, hidA, z_eq, compA_unpack cZ ha, compA_unpack hb pidPP.1, compA_unpack hb cZ,
    compA_unpack hb ha, compA_unpack hb (canonK_pcomp cZ ha), eqA_F hc (canonK_pcomp hb pidPP.1),
    eqA_F hc (canonK_pcomp hb cZ), eqA_F hc (canonK_pcomp hb ha),
    eqA_F hc (canonK_pcomp hb (canonK_pcomp cZ ha)), inK3]
  simp only [Bool.or_assoc]

theorem some_eq {a b c : ℕ} (ha : canonK 100 7 (mask 7) (100 * 7) a = true)
    (hb : canonK 100 7 (mask 7) (100 * 7) b = true)
    (hc : canonK 100 7 (mask 7) (100 * 7) c = true) :
    zasInSome (unpack 100 7 a) (unpack 100 7 b) (unpack 100 7 c) = inSome a b c := by
  rw [zasInSome, inSome, anyNP_eq]
  apply any_congr'
  intro j hj
  have hj' := List.mem_range.1 hj
  rw [eMem hj' ha, eMem hj' hb, eMem hj' hc]

theorem loop : (zasInvs.all fun a => zasMemL [idA 100, s5Z] a || zasInvs.all fun b =>
      !zasComm a b || zasMemL (zasK2 a) b ||
        (let k3 := zasK3 a b
         zasInvs.all fun c => !zasComm a c || !zasComm b c || zasMemL k3 c || zasInSome a b c)) =
    true := by
  rw [invs_all, ← uniq]
  apply allN_congr
  intro ja hja
  have ca := cI hja
  unfold uniqAt
  rw [CFSG.KC.ConjOrb.strictB_eq, memL2_eq ca, invs_all]
  congr 1
  apply allN_congr
  intro jb hjb
  have cb := cI hjb
  rw [CFSG.KC.ConjOrb.strictB_eq, comm_eq ca cb, k2_eq ca cb]
  dsimp only
  rw [invs_all]
  congr 1
  apply allN_congr
  intro jc hjc
  have cc := cI hjc
  rw [CFSG.KC.ConjOrb.strictB_eq, comm_eq ca cc, comm_eq cb cc, k3_eq ca cb cc, some_eq ca cb cc]

theorem fp_eq (p : ℕ) : zasFp (unpack 100 7 p) = fixK 100 7 p := fixCnt_eq p

theorem fixes_at {j : ℕ} (hj : j < 8) (h : (Nat.beq j 0 || Nat.beq j 5) = false) :
    ((zasEC j).pts.toList.any fun w => !eqA 100 w (idA 100) && zasFp w != zasFp s5Z) = true := by
  have h1 := allN_spec fixes j hj
  rw [h, Bool.false_or, anyNP_eq] at h1
  rw [listOf (ePin hj).2.1, List.any_map]
  refine (any_congr' fun i hi => ?_).trans h1
  have c := (ePin hj).2.2 i (List.mem_range.1 hi)
  simp only [Function.comp_apply]
  rw [hidA, eqA_F c pidPP.1, z_eq, fp_eq, fp_eq, bne, S0.beq_nat]

theorem conj_any : (zasTCert.pts.toList.any fun t => (List.range 4).all fun k =>
    zasMem (zasEC zasSpecIdx.2) (zasConj t (zasEGens zasSpecIdx.1)[k]!)) = true := by
  rw [listOf tPin.2, List.any_map]
  have h := conjE
  rw [anyNP_eq] at h
  refine (any_congr' fun i hi => ?_).trans (by rw [← nums'.2.1] at h; exact h)
  have hi' : i < 512 := by rw [← nums'.2.1]; exact List.mem_range.1 hi
  simp only [Function.comp_apply, zasSpecIdx]
  rw [← allN_range]
  apply allN_congr
  intro k hk
  rw [e_get (j := 0) (by norm_num) k hk, show 4 * 0 + k = k by omega, zasConj_unpack (ppTT hi')
    (pp_of_permB sz (perms'.2 _ (by omega))).1]
  exact eMem (t := pZ (TT.T i) (EA.F k)) (by norm_num) (canonK_pcomp (canonK_pcomp (ppTT hi').1
      (pp_of_permB sz (perms'.2 _ (by omega))).1) (ppTT hi').inv.1)

theorem zasUniqOK_true : zasUniqOK = true := by
  have hz1 : validA 100 s5Z = true := by rw [z_eq]; exact validA_unpack (and_of S0.zperm).1
  have hz2 : eqA 100 s5Z (idA 100) = false := by
    rw [z_eq, hidA, eqA_F cZ pidPP.1]; exact S0.prods'.2.1
  have hsz : (zasTCert.pts.size == 512) = true := by
    rw [tPin.2, Array.size_ofFn, nums'.2.1]; rfl
  have he : ((List.range 8).all fun j =>
      enumOK 100 (zasEGens j) zasEKeys (zasEC j) && (zasEC j).pts.size == 16 &&
        zasMem (zasEC j) s5Z) = true := by
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [(ePin hj').1, (ePin hj').2.1, Array.size_ofFn, z_eq, eMem hj' cZ, allN_spec zmem j hj']
    rfl
  have hf : ((List.range 8).all fun j => j == zasSpecIdx.1 || j == zasSpecIdx.2 ||
      (zasEC j).pts.toList.any fun w => !eqA 100 w (idA 100) && zasFp w != zasFp s5Z) = true := by
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    simp only [zasSpecIdx, S0.beq_nat]
    cases e : (Nat.beq j 0 || Nat.beq j 5)
    · rw [Bool.false_or]; exact fixes_at hj' e
    · rfl
  unfold zasUniqOK
  rw [hz1, hz2, tPin.1, hsz, he, loop, hf, conj_any]
  rfl

end CertificateChecks.KernelMisc.HS100.T

end
