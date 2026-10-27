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

theorem comm_fin (x : ℕ) (hx : canonK 100 7 (mask 7) (100 * 7) x = true) :
    decide (∀ i : Fin 4, eqA 100 (compA 100 (unpack 100 7 x) zasE0Gens[i.1]!)
      (compA 100 zasE0Gens[i.1]! (unpack 100 7 x)) = true) = allN 4 fun i => cK x (S0.EX.F i) := by
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff]
  constructor
  · intro h
    refine CFSG.KS.PackFld.allN_of_forall fun k hk => ?_
    have := h ⟨k, hk⟩
    rwa [e0_get k hk, ← commA, cK_eq hx (ppE hk).1] at this
  · intro h i
    have := allN_spec h i.1 i.2
    rwa [e0_get i.1 i.2, ← commA, cK_eq hx (ppE i.2).1]

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
  have h11 : (zasNCert.pts.toList.all fun x =>
      !decide (∀ i : Fin 4, eqA 100 (compA 100 x zasE0Gens[i.1]!)
        (compA 100 zasE0Gens[i.1]! x) = true) || zasMem zasE0Cert x) = true := by
    rw [listOf nPin, List.all_map, List.all_eq_true]
    intro t ht
    have ht' := List.mem_range.1 ht
    have h := allN_spec cent t ht'
    unfold centPt at h
    rw [Function.comp_apply, comm_fin _ (cNN t ht'), mem_e0 (cNN t ht')]
    exact h
  unfold i2ModelOK
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  rfl

end CertificateChecks.KernelMisc.HS100.N

end
