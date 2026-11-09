module

public import Certificates.Kernel.Misc.Perm.HS100.NChecks
public import Certificates.Kernel.Misc.Perm.HS100.S0Glue
import CFSG.Certificates.Kernel.Spor.PackFld

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.N

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.Zassenhaus
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2 CFSG.KC.Misc.HexFlat
open CFSG.KC.Misc.ArrEnum (permB pp_of_permB memK)
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.Five (eqA_F hidA pidPP and_of commA_F)
open CertificateChecks.KernelMisc.HS100.S0 (e0_get e0Pin listOf getOf any_eq cE0 cK cK_eq keysOK)

theorem perms' : (∀ k < 2, permB 100 7 (NX.F k) = true) ∧ (∀ k < 2, permB 100 7 (RX k) = true) :=
  ⟨fun k hk => allN_spec (and_of perms).1 k hk, fun k hk => allN_spec (and_of perms).2 k hk⟩

theorem nums' : NN.ng = 2 ∧ NN.N = 11520 ∧ ∀ k < 2, NN.G k = NX.F k := by
  have h := nums
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1, h.1.2, fun k hk => Nat.eq_of_beq_eq_true (allN_spec h.2 k hk)⟩

theorem n_get : ∀ k < 2, zasNGens[k]! = unpack 100 7 (NX.F k) := by
  intro k hk
  rw [zasNGens, zasGens, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn, NX.eq]
  exact hexTable3_sound NX.all k hk

theorem r_get : ∀ k < 2, i2R[k]! = unpack 100 7 (RX k) := fun k hk => (rx_eq ⟨k, hk⟩).symm

theorem cNX {k : ℕ} (hk : k < 2) : canonK 100 7 (mask 7) (100 * 7) (NX.F k) = true :=
  (pp_of_permB sz (perms'.1 k hk)).1

theorem cRX {k : ℕ} (hk : k < 2) : canonK 100 7 (mask 7) (100 * 7) (RX k) = true :=
  (pp_of_permB sz (perms'.2 k hk)).1

theorem ppE {i : ℕ} (hi : i < 4) : PP 100 7 (S0.EX.F i) :=
  pp_of_permB sz (allN_spec (and_of S0.zperm).2 i hi)

theorem cNN : ∀ i < NN.N, canonK 100 7 (mask 7) (100 * 7) (NN.T i) = true := bfsK_canon NN.ok

theorem nPin : zasNCert.pts = Array.ofFn (n := NN.N) fun i => unpack 100 7 (NN.T i.val) :=
  enumBfs_pts_base (by rw [nums'.1]; rfl)
    (fun k hk => by rw [nums'.1] at hk; rw [n_get k hk, nums'.2.2 k hk]) NN.ok
    (by decide) keys (by rw [nums'.2.1]; norm_num)

theorem zasConj_unpack {p q : ℕ} (hp : PP 100 7 p) (hq : canonK 100 7 (mask 7) (100 * 7) q = true) :
    zasConj (unpack 100 7 p) (unpack 100 7 q) = unpack 100 7 (pZ p q) := by
  rw [zasConj, invCand_PP hp, compA_unpack hp.1 hq, compA_unpack (canonK_pcomp hp.1 hq) hp.inv.1]
  rfl

theorem selK_pp {e : ℕ} (he : PP 100 7 e) (b : ZMod 2) : PP 100 7 (selK e b) := by
  unfold selK
  split_ifs
  · exact pidPP
  · exact he

theorem selA_unpack {e : ℕ} (b : ZMod 2) :
    selA (unpack 100 7 e) b = unpack 100 7 (selK e b) := by
  unfold selA selK
  split_ifs
  · exact hidA
  · rfl

theorem vecEA_unpack (v : Fin 4 → ZMod 2) : vecEA v = unpack 100 7 (vecEK v) := by
  have c := fun (i : ℕ) (hi : i < 4) (b : ZMod 2) => (selK_pp (ppE hi) b).1
  unfold vecEA vecEK
  rw [e0_get 0 (by norm_num), e0_get 1 (by norm_num), e0_get 2 (by norm_num),
    e0_get 3 (by norm_num), selA_unpack, selA_unpack, selA_unpack, selA_unpack, hidA,
    compA_unpack (c 3 (by norm_num) _) pidPP.1,
    compA_unpack (c 2 (by norm_num) _) (canonK_pcomp (c 3 (by norm_num) _) pidPP.1),
    compA_unpack (c 1 (by norm_num) _)
      (canonK_pcomp (c 2 (by norm_num) _) (canonK_pcomp (c 3 (by norm_num) _) pidPP.1)),
    compA_unpack (c 0 (by norm_num) _) (canonK_pcomp (c 1 (by norm_num) _)
      (canonK_pcomp (c 2 (by norm_num) _) (canonK_pcomp (c 3 (by norm_num) _) pidPP.1)))]

theorem vecEK_canon (v : Fin 4 → ZMod 2) : canonK 100 7 (mask 7) (100 * 7) (vecEK v) = true := by
  have c := fun (i : ℕ) (hi : i < 4) (b : ZMod 2) => (selK_pp (ppE hi) b).1
  exact canonK_pcomp (c 0 (by norm_num) _) (canonK_pcomp (c 1 (by norm_num) _)
    (canonK_pcomp (c 2 (by norm_num) _) (canonK_pcomp (c 3 (by norm_num) _) pidPP.1)))

theorem conj_vec {p : ℕ} (hp : PP 100 7 p) {i : ℕ} (hi : i < 4) (v : Fin 4 → ZMod 2)
    (h : Nat.beq (pZ p (S0.EX.F i)) (vecEK v) = true) :
    eqA 100 (zasConj (unpack 100 7 p) zasE0Gens[i]!) (vecEA v) = true := by
  rw [e0_get i hi, zasConj_unpack hp (ppE hi).1, vecEA_unpack,
    eqA_F (p := pZ p (S0.EX.F i)) (canonK_pcomp (canonK_pcomp hp.1 (ppE hi).1) hp.inv.1)
      (vecEK_canon v)]
  exact h

theorem mem_e0 {t : ℕ} (ht : canonK 100 7 (mask 7) (100 * 7) t = true) :
    zasMem zasE0Cert (unpack 100 7 t) = memK S0.E0.N S0.E0.T t := by
  rw [zasMem, listOf e0Pin.2]
  exact any_eq cE0 ht

theorem mem_n {t : ℕ} (ht : canonK 100 7 (mask 7) (100 * 7) t = true) :
    zasMem zasNCert (unpack 100 7 t) = memK NN.N NN.T t := by
  rw [zasMem, listOf nPin]
  exact any_eq cNN ht

theorem mems' : memK S0.E0.N S0.E0.T (pcomp 100 7 (mask 7) (RX 0) (RX 0)) = true ∧
    memK S0.E0.N S0.E0.T (pcomp 100 7 (mask 7) (RX 1) (RX 1)) = true ∧
    memK S0.E0.N S0.E0.T (pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (RX 0) (RX 1))
      (pcomp 100 7 (mask 7) (RX 0) (RX 1))) = true ∧
    memK NN.N NN.T (RX 0) = true ∧ memK NN.N NN.T (RX 1) = true := by
  have h := mems
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem repsChainN_spec : ∀ (L : List ℕ) (p : ℕ), repsChainN L p = true →
    (∀ t ∈ L, t < 11520 ∧ p < actKN (NN.T t)) ∧
      L.Pairwise fun a b => actKN (NN.T a) < actKN (NN.T b)
  | [], _, _ => ⟨fun _ h => by simp at h, List.Pairwise.nil⟩
  | t :: L, p, h => by
    change (Nat.blt t 11520 && Nat.blt p (actKN (NN.T t)) &&
      repsChainN L (actKN (NN.T t))) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := repsChainN_spec L _ h3
    refine ⟨fun s hs => ?_, List.Pairwise.cons (fun s hs => (ih1 s hs).2) ih2⟩
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨h1, h2⟩
    · exact ⟨(ih1 s hs).1, h2.trans (ih1 s hs).2⟩

theorem ppNN : ∀ a < NN.N, PP 100 7 (NN.T a) :=
  PP_pts NN.ok fun k hk => by
    have hk' : k < 2 := by rwa [nums'.1] at hk
    have hp := pp_of_permB sz (perms'.1 k hk')
    rw [nums'.2.2 k hk']
    exact CFSG.KS.PinvS.permOK_pinvS hp.1 hp.2

theorem conjN_pts {a : ℕ} (ha : a < 11520) {i : ℕ} (hi : i < 4) :
    zasConj zasNCert.pts[a]! zasE0Gens[i]! = unpack 100 7 (pZ (NN.T a) (S0.EX.F i)) := by
  have ha' : a < NN.N := by rw [nums'.2.1]; exact ha
  rw [getOf nPin a ha', e0_get i hi]
  exact zasConj_unpack (ppNN a ha') (ppE hi).1

theorem pZpt_canon {a : ℕ} (ha : a < 11520) {i : ℕ} (hi : i < 4) :
    canonK 100 7 (mask 7) (100 * 7) (pZ (NN.T a) (S0.EX.F i)) = true := by
  have hp := ppNN a (by rw [nums'.2.1]; exact ha)
  exact canonK_pcomp (canonK_pcomp hp.1 (ppE hi).1) hp.inv.1

theorem repsPw : i2Reps.Pairwise fun a b => ¬ ∀ i : Fin 4,
    eqA 100 (zasConj zasNCert.pts[a]! zasE0Gens[i.1]!)
      (zasConj zasNCert.pts[b]! zasE0Gens[i.1]!) = true := by
  obtain ⟨h1, h2⟩ := repsChainN_spec _ _ repsOKN
  refine h2.imp_of_mem fun {a b} ha hb hab heq => (Nat.ne_of_lt hab) ?_
  have hz : ∀ i < 4, pZ (NN.T a) (S0.EX.F i) = pZ (NN.T b) (S0.EX.F i) := fun i hi => by
    have := heq ⟨i, hi⟩
    dsimp only at this
    rw [conjN_pts (h1 a ha).1 hi, conjN_pts (h1 b hb).1 hi,
      eqA_F (pZpt_canon (h1 a ha).1 hi) (pZpt_canon (h1 b hb).1 hi)] at this
    exact Nat.eq_of_beq_eq_true this
  unfold actKN
  rw [hz 0 (by norm_num), hz 1 (by norm_num), hz 2 (by norm_num), hz 3 (by norm_num)]

theorem i2ModelOK_true : i2ModelOK = true := by
  have pN := fun (k : ℕ) (hk : k < 2) => pp_of_permB sz (perms'.1 k hk)
  have pR := fun (k : ℕ) (hk : k < 2) => pp_of_permB sz (perms'.2 k hk)
  have h1 : decide (∀ j : Fin 2, ∀ i : Fin 4,
      eqA 100 (zasConj zasNGens[j.1]! zasE0Gens[i.1]!) (vecEA (rho j i)) = true) = true := by
    refine decide_eq_true fun j i => ?_
    rw [n_get j.1 j.2]
    exact conj_vec (pN j.1 j.2) i.2 _ (rhoK j i)
  have h2 : decide (∀ i : Fin 4,
      eqA 100 (zasConj i2R[0]! zasE0Gens[i.1]!) (vecEA (kx i)) = true) = true := by
    refine decide_eq_true fun i => ?_
    rw [r_get 0 (by norm_num)]
    exact conj_vec (pR 0 (by norm_num)) i.2 _ (kxK i)
  have h3 : decide (∀ i : Fin 4,
      eqA 100 (zasConj i2R[1]! zasE0Gens[i.1]!) (vecEA (ky i)) = true) = true := by
    refine decide_eq_true fun i => ?_
    rw [r_get 1 (by norm_num)]
    exact conj_vec (pR 1 (by norm_num)) i.2 _ (kyK i)
  have c0 := cRX (k := 0) (by norm_num)
  have c1 := cRX (k := 1) (by norm_num)
  have h4 : validA 100 i2R[0]! = true := by
    rw [r_get 0 (by norm_num)]; exact validA_unpack (perms'.2 0 (by norm_num))
  have h5 : validA 100 i2R[1]! = true := by
    rw [r_get 1 (by norm_num)]; exact validA_unpack (perms'.2 1 (by norm_num))
  have h6 : zasMem zasE0Cert (compA 100 i2R[0]! i2R[0]!) = true := by
    rw [r_get 0 (by norm_num), compA_unpack c0 c0, mem_e0 (canonK_pcomp c0 c0)]
    exact mems'.1
  have h7 : zasMem zasE0Cert (compA 100 i2R[1]! i2R[1]!) = true := by
    rw [r_get 1 (by norm_num), compA_unpack c1 c1, mem_e0 (canonK_pcomp c1 c1)]
    exact mems'.2.1
  have h8 : zasMem zasE0Cert (compA 100 (compA 100 i2R[0]! i2R[1]!)
      (compA 100 i2R[0]! i2R[1]!)) = true := by
    rw [r_get 0 (by norm_num), r_get 1 (by norm_num), compA_unpack c0 c1,
      compA_unpack (canonK_pcomp c0 c1) (canonK_pcomp c0 c1),
      mem_e0 (canonK_pcomp (canonK_pcomp c0 c1) (canonK_pcomp c0 c1))]
    exact mems'.2.2.1
  have h9 : zasMem zasNCert i2R[0]! = true := by
    rw [r_get 0 (by norm_num), mem_n c0]; exact mems'.2.2.2.1
  have h10 : zasMem zasNCert i2R[1]! = true := by
    rw [r_get 1 (by norm_num), mem_n c1]; exact mems'.2.2.2.2
  obtain ⟨hc, -⟩ := repsChainN_spec _ _ repsOKN
  have hsz : zasNCert.pts.size = 11520 := by rw [nPin, Array.size_ofFn, nums'.2.1]
  have h11 : (i2Reps.length == 720) = true := by rfl
  have h12 : (i2Reps.all fun k => decide (k < zasNCert.pts.size)) = true :=
    List.all_eq_true.2 fun k hk => decide_eq_true (by rw [hsz]; exact (hc k hk).1)
  unfold i2ModelOK
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, decide_eq_true repsPw]
  rfl

end CertificateChecks.KernelMisc.HS100.N

end
